#!/usr/bin/env python3
"""Catalog, inspect, export, and safely edit NBA 2K20 Android IFF resources."""

from __future__ import annotations

import argparse
import bisect
from collections import Counter
import dataclasses
import io
import json
import math
import os
import queue
import re
import sqlite3
import struct
import sys
import tempfile
import threading
import time
import zlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

APP_DIR = Path(__file__).resolve().parent
VENDOR_DIR = APP_DIR / "vendor"
OBB_TOOLS_DIR = APP_DIR / "obb_tools"

# The archive contains desktop native wheels for Windows. They must never be
# placed ahead of Pydroid's Android packages on Android/Linux.
if sys.platform == "win32":
    sys.path.insert(0, str(VENDOR_DIR))
sys.path.insert(0, str(OBB_TOOLS_DIR))

from PIL import Image, ImageDraw  # noqa: E402
ImageTk = None  # Tkinter is unavailable on Android; the Android UI is native.

# Pure-Python ETC2 fallback for Android/Pydroid 3. This keeps ETC2 preview and
# PNG/JPEG export working even when the optional native decoder cannot load.
try:
    from pure_etc2 import (
        decode_etc2 as decode_etc2_pure,
        decode_etc2_rgba8 as decode_etc2_rgba8_pure,
        encode_etc2_rgb as encode_etc2_rgb_pure,
        encode_etc2_rgba8 as encode_etc2_rgba8_pure,
    )
except Exception:
    decode_etc2_pure = None
    decode_etc2_rgba8_pure = None
    encode_etc2_rgb_pure = None
    encode_etc2_rgba8_pure = None

# ETC2 codecs are optional at startup. Missing native codecs must not make the
# entire Android app crash; RGB565/RGBA4444/RAW IFF operations remain usable.
try:
    import texture2ddecoder  # noqa: E402
except Exception:
    texture2ddecoder = None
try:
    import etcpak  # noqa: E402
except Exception:
    etcpak = None

from direct_obb import DirectObbSession, EDITABLE_TYPES  # noqa: E402

try:
    from etc2_repair import decode_etc2_auto, decode_etc2_layout
except Exception:
    decode_etc2_auto = None
    decode_etc2_layout = None


TYPE_COMPRESSED = b"\x94\xef\x3b\xff"
TYPE_ZLIB = b"ZLIB"
HEADER_SIZE = 0xF0
FORMATS = (2, 4, 15, 16)
FORMAT_RGBA8888_RAW = 17
FORMAT_NAMES = {
    2: "RGB565",
    4: "RGBA4444",
    15: "ETC2 RGB",
    16: "ETC2 RGBA8",
    FORMAT_RGBA8888_RAW: "RGBA8888",
}
DIMENSIONS = (4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
RESOURCE_PREVIEW_BYTES = 512
_MANIFEST_CACHE: dict[Path, tuple[int, dict[str, object], dict[Path, dict[str, object]]]] = {}
CATALOG_FILENAME = ".nba2k20_iff_catalog.sqlite"
CATALOG_PARSER_VERSION = "5"

# Uniform IFFs keep two texture payloads in a descriptor-less streamed block.
# The layout was verified across the UH/UA team set: a 512x512 RGBA4444
# normal/wordmark atlas (including its mip chain and two alignment bytes), then
# a 512x512 ETC2 RGB color/logo atlas.  These resources were previously shown
# only as one opaque VRAM block, which hid the team chest wordmark from the
# texture editor.
UNIFORM_STREAM_BLOCK_SIZE = 873_828
UNIFORM_NORMAL_STREAM_SIZE = 699_052
UNIFORM_NORMAL_ENCODED_SIZE = 699_050
UNIFORM_COLOR_STREAM_OFFSET = UNIFORM_NORMAL_STREAM_SIZE
UNIFORM_COLOR_STREAM_SIZE = 174_776
# uniform.py exposed a 256x256 image candidate at this decoded offset, but its
# original "detection" accepted every byte range Pillow could read.  The manager
# validates alpha behavior, RGB activity/diversity, spatial coherence, and block
# containment before labelling the bytes RGBA8888.  This also recognizes genuine
# non-uniform images that use the same layout without mislabelling random data.
RAW_RGBA8888_PROBE_OFFSET = 662_128
RAW_RGBA8888_PROBE_WIDTH = 256
RAW_RGBA8888_PROBE_HEIGHT = 256
RAW_RGBA8888_PROBE_SIZE = RAW_RGBA8888_PROBE_WIDTH * RAW_RGBA8888_PROBE_HEIGHT * 4
UNIFORM_IFF_NAME = re.compile(
    r"^(?:UH|UA)\d{3}(?:[_-][A-Za-z0-9]+)*\.IFF(?:\.decompressed)?$", re.I
)
# Several large front-end IFFs store their tagged texture bank at the end of a
# VRAM block. Their tags are relative to the bank, not the physical block.
# Treating those tags as block-relative still produces correctly sized ETC/RGBA
# data, but it is unrelated bytes and therefore previews as multicolored
# scratch. Require multiple archive-specific hashes before selecting this
# layout; courts such as F022 use a genuinely block-relative bank and must not
# be end-anchored.
VERIFIED_END_ANCHORED_TEXTURE_BANKS = (
    frozenset(
        {
            0xD917385A,  # FRONTEND_SYNC: rear/full menu portrait
            0x5666ABC9,  # FRONTEND_SYNC: post-selection loading screen
            0x14DB7FA0,  # FRONTEND_SYNC: active menu player cutout
        }
    ),
    frozenset(
        {
            0xED459A3E,  # GOOEYFRONTEND structural sentinel
            0xF3EBECD5,
            0x1AECDAC9,
            0x83E58B73,
        }
    ),
    frozenset(
        {
            0xAD1FCC82,  # GLOBAL structural sentinel
            0xCDD84567,
            0xBADF75F1,
            0xD82EF1D7,
        }
    ),
)
# This multi-panel main-menu atlas is stored twice inside FRONTEND_SYNC.IFF:
# one descriptor-backed editor copy and one serialized runtime copy. Replacing
# only the descriptor-backed payload previews correctly in the manager but the
# game continues to render the unchanged runtime copy. The two copies are
# updated together only when their complete original encoded bytes match.
LINKED_RUNTIME_TEXTURE_HASHES = {
    0xBBF60004,  # main-menu five-panel atlas
}


def find_iff_files(folder: Path) -> list[Path]:
    folder = folder.resolve()
    if not folder.is_dir():
        raise ValueError(f"IFF folder was not found: {folder}")
    files = [
        path
        for path in folder.rglob("*")
        if path.is_file()
        and path.name.lower().endswith((".iff", ".iff.decompressed"))
    ]
    return sorted(files, key=lambda path: str(path.relative_to(folder)).lower())


def readable_size(size: int) -> str:
    value = float(size)
    for unit in ("B", "KB", "MB", "GB"):
        if value < 1024 or unit == "GB":
            return f"{value:.0f} {unit}" if unit == "B" else f"{value:.1f} {unit}"
        value /= 1024
    return f"{size} B"


@dataclasses.dataclass
class TextureRecord:
    number: int
    header_offset: int
    texture_hash: int
    format_id: int
    width: int
    height: int
    tagged_offset: int
    payload_size: int
    payload_offset: int | None
    location: str
    allocation_size: int = 0
    encoded_size: int = 0
    uses_mip_chain: bool = False
    error: str | None = None
    label: str = ""
    has_header: bool = True
    decode_layout: str = "standard"
    decode_score: float | None = None

    def as_dict(self) -> dict[str, object]:
        return {
            "number": self.number,
            "header_offset": f"0x{self.header_offset:X}" if self.has_header else None,
            "texture_hash": f"0x{self.texture_hash:08X}",
            "format_id": self.format_id,
            "format": FORMAT_NAMES[self.format_id],
            "width": self.width,
            "height": self.height,
            "tagged_offset": f"0x{self.tagged_offset:X}",
            "payload_size": self.payload_size,
            "payload_offset": (
                f"0x{self.payload_offset:X}" if self.payload_offset is not None else None
            ),
            "location": self.location,
            "allocation_size": self.allocation_size,
            "encoded_size": self.encoded_size,
            "uses_mip_chain": self.uses_mip_chain,
            "error": self.error,
            "label": self.label,
            "has_header": self.has_header,
            "decode_layout": self.decode_layout,
            "decode_score": self.decode_score,
        }


@dataclasses.dataclass
class ResourceRecord:
    """One exact byte range exposed by the generic resource browser.

    NBA 2K IFFs do not carry a normal filename for every serialized object.
    Identified embedded files get a useful extension; everything else remains
    honestly labelled as a container block or unclassified binary range.
    """

    number: int
    kind: str
    name: str
    offset: int
    size: int
    extension: str
    details: str
    confidence: str = "exact"
    texture_number: int | None = None
    container: bool = False

    @property
    def end(self) -> int:
        return self.offset + self.size

    def as_dict(self) -> dict[str, object]:
        return {
            "number": self.number,
            "kind": self.kind,
            "name": self.name,
            "offset": f"0x{self.offset:X}",
            "size": self.size,
            "extension": self.extension,
            "details": self.details,
            "confidence": self.confidence,
            "texture_number": self.texture_number,
            "container": self.container,
        }


@dataclasses.dataclass
class GpuBufferRecord:
    number: int
    metadata_offset: int
    block_index: int
    local_offset: int
    payload_offset: int
    size: int
    stride: int
    element_count: int
    score: int

    def as_dict(self) -> dict[str, object]:
        return {
            "number": self.number,
            "metadata_offset": f"0x{self.metadata_offset:X}",
            "block": self.block_index + 1,
            "local_offset": f"0x{self.local_offset:X}",
            "payload_offset": f"0x{self.payload_offset:X}",
            "size": self.size,
            "stride": self.stride,
            "element_count": self.element_count,
            "score": self.score,
        }


@dataclasses.dataclass
class MeshRecord:
    """A conservatively validated indexed mesh decoded from one GPU stream."""

    number: int
    buffer_number: int
    vertex_offset: int
    vertex_stride: int
    vertex_count: int
    position_offset: int
    index_offset: int
    index_count: int
    triangle_count: int
    topology: str
    confidence: str
    details: str

    def as_dict(self) -> dict[str, object]:
        return {
            "number": self.number,
            "buffer_number": self.buffer_number,
            "vertex_offset": f"0x{self.vertex_offset:X}",
            "vertex_stride": self.vertex_stride,
            "vertex_count": self.vertex_count,
            "position_offset": self.position_offset,
            "index_offset": f"0x{self.index_offset:X}",
            "index_count": self.index_count,
            "triangle_count": self.triangle_count,
            "topology": self.topology,
            "confidence": self.confidence,
            "details": self.details,
        }


@dataclasses.dataclass
class WrapperBlock:
    position: int
    unpacked_size: int
    # Physical byte span occupied by this block in the source file.  Most
    # OBB IFFs store this value in the ZLIB header, but some DAT-style loose
    # overrides store only the compressed payload length there.
    stored_size: int
    declared_stored_size: int
    flags: int
    unpacked_offset: int


@dataclasses.dataclass
class WrapperInfo:
    first_offset: int
    compressed_wrapper: bool
    blocks: list[WrapperBlock]


@dataclasses.dataclass
class OpenedIff:
    path: Path
    source_size: int
    wrapper: str
    source_raw: bytes
    original_data: bytes
    data: bytearray
    block_sizes: list[int]
    boundary_source: str
    textures: list[TextureRecord]
    gpu_buffers: list[GpuBufferRecord]
    meshes: list[MeshRecord]
    resources: list[ResourceRecord]
    wrapper_info: WrapperInfo | None
    # Expensive model/resource analysis is loaded on demand.  This keeps the
    # common texture-editing workflow fast on Android/Pydroid while preserving
    # the full analysis when the corresponding tab is opened.
    deep_analysis_loaded: bool = False
    resource_analysis_loaded: bool = False

    def summary(self) -> dict[str, object]:
        return {
            "file": str(self.path),
            "source_size": self.source_size,
            "wrapper": self.wrapper,
            "decompressed_size": len(self.data),
            "decompressed_block_sizes": self.block_sizes,
            "block_boundary_source": self.boundary_source,
            "texture_count": len(self.textures),
            "decodable_texture_count": sum(
                texture.payload_offset is not None for texture in self.textures
            ),
            "textures": [texture.as_dict() for texture in self.textures],
            "gpu_buffer_count": len(self.gpu_buffers),
            "gpu_buffers": [buffer.as_dict() for buffer in self.gpu_buffers],
            "mesh_count": len(self.meshes),
            "meshes": [mesh.as_dict() for mesh in self.meshes],
            "resource_count": len(self.resources),
            "resources": [resource.as_dict() for resource in self.resources],
        }


def payload_size(format_id: int, width: int, height: int) -> int:
    if format_id == FORMAT_RGBA8888_RAW:
        return width * height * 4
    if format_id in (2, 4):
        return width * height * 2
    blocks_wide = max(1, (width + 3) // 4)
    blocks_high = max(1, (height + 3) // 4)
    if format_id == 15:
        return blocks_wide * blocks_high * 8
    if format_id == 16:
        return blocks_wide * blocks_high * 16
    raise ValueError(f"unsupported texture format {format_id}")


def mip_chain_size(format_id: int, width: int, height: int) -> int:
    total = 0
    while True:
        total += payload_size(format_id, width, height)
        if width == 1 and height == 1:
            return total
        width = max(1, width // 2)
        height = max(1, height // 2)


def decompress_wrapper(
    raw: bytes,
) -> tuple[bytes, list[int], str, WrapperInfo | None]:
    if raw[:4] == TYPE_COMPRESSED:
        if len(raw) < 8:
            raise ValueError("truncated 2K compressed IFF wrapper")
        position = struct.unpack_from("<I", raw, 4)[0]
        if position < 8 or position >= len(raw):
            raise ValueError(f"invalid compressed payload offset 0x{position:X}")
        wrapper = "2K compressed IFF"
        compressed_wrapper = True
    elif raw[:4] == TYPE_ZLIB:
        position = 0
        wrapper = "2K ZLIB stream"
        compressed_wrapper = False
    else:
        return raw, [len(raw)], "decompressed IFF", None

    chunks: list[bytes] = []
    blocks: list[WrapperBlock] = []
    first_offset = position
    unpacked_offset = 0
    while position + 16 <= len(raw) and raw[position : position + 4] == TYPE_ZLIB:
        unpacked_size, declared_stored_size, _flags = struct.unpack_from(
            ">III", raw, position + 4
        )
        if unpacked_size <= 0 or declared_stored_size <= 0:
            raise ValueError(f"invalid ZLIB block at 0x{position:X}")

        # Let zlib identify the exact end of its own stream.  DAT loose-file
        # tools in the wild use both meanings for the stored-size field:
        # either the complete ZLIB block span (normal OBB convention), or the
        # compressed payload length without the 16-byte header.  A strict
        # subtraction of 16 rejects the latter even though the data is valid.
        payload = raw[position + 16 :]
        decoder = zlib.decompressobj()
        try:
            chunk = decoder.decompress(payload)
            chunk += decoder.flush()
        except zlib.error as error:
            raise ValueError(f"invalid ZLIB stream at 0x{position:X}: {error}") from error
        if not decoder.eof:
            raise ValueError(f"truncated ZLIB stream at 0x{position:X}")
        consumed_payload = len(payload) - len(decoder.unused_data)

        if (
            declared_stored_size >= 16
            and consumed_payload <= declared_stored_size - 16
        ):
            # Standard wrapper: stored size includes the 16-byte header and
            # may include zero padding reserved for in-place editing.
            stored_size = declared_stored_size
        elif consumed_payload <= declared_stored_size:
            # DAT loose override: stored size is the payload capacity only.
            stored_size = 16 + declared_stored_size
        else:
            # Recover a malformed size conservatively from the complete zlib
            # stream.  The decoded-size check below still protects parsing.
            stored_size = 16 + consumed_payload
        if position + stored_size > len(raw):
            raise ValueError(f"invalid ZLIB block span at 0x{position:X}")
        if len(chunk) != unpacked_size:
            raise ValueError(
                f"ZLIB block at 0x{position:X} decoded to {len(chunk)} bytes, "
                f"expected {unpacked_size}"
            )
        chunks.append(chunk)
        blocks.append(
            WrapperBlock(
                position=position,
                unpacked_size=unpacked_size,
                stored_size=stored_size,
                declared_stored_size=declared_stored_size,
                flags=_flags,
                unpacked_offset=unpacked_offset,
            )
        )
        unpacked_offset += unpacked_size
        position += stored_size
    if not chunks:
        raise ValueError("compressed IFF contains no readable ZLIB blocks")
    return (
        b"".join(chunks),
        [len(chunk) for chunk in chunks],
        wrapper,
        WrapperInfo(first_offset, compressed_wrapper, blocks),
    )


def _valid_sizes(values: object, total: int) -> list[int] | None:
    if not isinstance(values, list) or not values:
        return None
    if not all(isinstance(value, int) and value > 0 for value in values):
        return None
    return values if sum(values) == total else None


def detect_legacy_2k_wrapper(raw: bytes) -> tuple[list[tuple[int, int]], str] | None:
    """Recognize older 94 EF 3B FF IFF containers without ZLIB records."""
    if raw[:4] != TYPE_COMPRESSED or len(raw) < 0x20:
        return None
    header_end = struct.unpack_from("<I", raw, 4)[0]
    if header_end < 0x20 or header_end > min(len(raw), 0x10000):
        return None

    # Header-described payload ranges appear as little-endian offset/size
    # pairs. Build every plausible pair, then find an exact partition from
    # header_end to EOF. This avoids trusting arbitrary small integers in the
    # header as sizes.
    candidates: dict[int, set[int]] = {}
    values = [struct.unpack_from("<I", raw, off)[0] for off in range(0, header_end - 3, 4)]
    for value in values:
        if value < header_end or value >= len(raw):
            continue
        for size in values:
            if size > 0 and value + size <= len(raw):
                candidates.setdefault(value, set()).add(size)

    first_sizes = sorted(candidates.get(header_end, ()), reverse=True)
    def walk(cursor: int, ranges: list[tuple[int, int]]) -> list[tuple[int, int]] | None:
        if cursor == len(raw):
            return ranges
        if len(ranges) >= 32:
            return None
        for size in sorted(candidates.get(cursor, ()), reverse=True):
            result = walk(cursor + size, ranges + [(cursor, size)])
            if result is not None:
                return result
        return None

    for size in first_sizes:
        result = walk(header_end + size, [(header_end, size)])
        if result is not None and len(result) >= 2:
            return result, "legacy 2K header-described blocks"
    return None


def stored_wrapper_block_sizes(raw: bytes) -> list[int] | None:
    if raw[:4] not in (TYPE_COMPRESSED, TYPE_ZLIB):
        return None
    try:
        _data, sizes, _wrapper, info = decompress_wrapper(raw)
    except (ValueError, zlib.error):
        return None
    return sizes if info is not None else None


def _cached_manifest(
    manifest_path: Path, parent: Path
) -> tuple[dict[str, object], dict[Path, dict[str, object]]]:
    resolved = manifest_path.resolve()
    modified = manifest_path.stat().st_mtime_ns
    cached = _MANIFEST_CACHE.get(resolved)
    if cached is not None and cached[0] == modified:
        return cached[1], cached[2]
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    records: dict[Path, dict[str, object]] = {}
    for record in manifest.get("entries", []):
        if not isinstance(record, dict) or not isinstance(record.get("file"), str):
            continue
        records[(parent / str(record["file"])).resolve()] = record
    _MANIFEST_CACHE[resolved] = (modified, manifest, records)
    return manifest, records


def find_recorded_block_sizes(path: Path, total: int) -> tuple[list[int] | None, str]:
    resolved = path.resolve()
    sidecar = path.with_suffix(path.suffix + ".viewer.json")
    if sidecar.is_file():
        try:
            record = json.loads(sidecar.read_text(encoding="utf-8"))
            sizes = _valid_sizes(record.get("decompressed_block_sizes"), total)
            if sizes:
                return sizes, str(sidecar)
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            pass
    ancestors = [path.parent, *list(path.parents)[1:5]]
    missing_reason = "not recorded"
    for parent in ancestors:
        manifest_path = parent / "manifest.json"
        if not manifest_path.is_file():
            continue
        try:
            manifest, records = _cached_manifest(manifest_path, parent)
            record = records.get(resolved)
            if record is not None:
                sizes = _valid_sizes(record.get("decompressed_block_sizes"), total)
                if sizes:
                    return sizes, str(manifest_path)
                source_text = manifest.get("source_obb")
                block = record.get("block")
                length = record.get("length")
                if (
                    isinstance(source_text, str)
                    and isinstance(block, int)
                    and isinstance(length, int)
                    and block >= 0
                    and length > 0
                ):
                    source_obb = Path(source_text)
                    if source_obb.is_file():
                        try:
                            with source_obb.open("rb") as stream:
                                stream.seek(block * 2048)
                                raw_entry = stream.read(length)
                            recovered = _valid_sizes(
                                stored_wrapper_block_sizes(raw_entry), total
                            )
                            if recovered:
                                return (
                                    recovered,
                                    f"{manifest_path} (recovered from source OBB)",
                                )
                        except OSError:
                            pass
                    else:
                        missing_reason = (
                            "older extraction manifest has no block sizes and its "
                            "source OBB is unavailable"
                        )
        except (KeyError, OSError, ValueError, TypeError, json.JSONDecodeError):
            continue

    iff_name = re.sub(r"\.decompressed$", "", path.name, flags=re.IGNORECASE)
    for parent in ancestors:
        known_manifests = (
            (parent / "COURT_RESOURCE_MANIFEST.json", "teams"),
            (parent / "UNIFORM_RESOURCE_MANIFEST.json", "uniforms"),
        )
        for manifest_path, collection in known_manifests:
            if not manifest_path.is_file():
                continue
            try:
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                for record in manifest.get(collection, []):
                    if str(record.get("iff", "")).lower() != iff_name.lower():
                        continue
                    sizes = _valid_sizes(
                        [record.get("dram_size"), record.get("vram_size")], total
                    )
                    if sizes:
                        return sizes, str(manifest_path)
            except (OSError, ValueError, TypeError, json.JSONDecodeError):
                continue

        for text_manifest in (parent / "manifest.txt", parent / "png" / "manifest.txt"):
            if not text_manifest.is_file():
                continue
            try:
                text = text_manifest.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            match = re.search(r"^vram_base\s*=\s*(0x[0-9a-f]+|\d+)", text, re.I | re.M)
            if match:
                vram_base = int(match.group(1), 0)
                sizes = _valid_sizes([vram_base, total - vram_base], total)
                if sizes:
                    return sizes, str(text_manifest)
    return None, missing_reason


def scan_headers(data: bytes) -> list[dict[str, int]]:
    descriptors: list[dict[str, int]] = []
    # Search the invariant marker in native bytes.find() instead of executing
    # Python code at every four-byte position. This matters when cataloguing
    # the full 7+ GB extracted IFF set.
    marker = struct.pack("<I", 0x20)
    search = 0x28
    candidates: list[int] = []
    while True:
        marker_offset = data.find(marker, search)
        if marker_offset < 0:
            break
        offset = marker_offset - 0x28
        if offset >= 0 and offset % 4 == 0 and offset + HEADER_SIZE <= len(data):
            candidates.append(offset)
        search = marker_offset + 1
    for offset in candidates:
        format_id = struct.unpack_from("<I", data, offset + 0x10)[0]
        if format_id not in FORMATS:
            continue
        if struct.unpack_from("<I", data, offset + 0x14)[0] != format_id:
            continue
        if struct.unpack_from("<I", data, offset + 0x28)[0] != 0x20:
            continue
        width, height = struct.unpack_from("<HH", data, offset + 0xC8)
        tagged = struct.unpack_from("<I", data, offset + 0xD8)[0]
        if width not in DIMENSIONS or height not in DIMENSIONS or tagged < 1:
            continue
        descriptors.append(
            {
                "header_offset": offset,
                "texture_hash": struct.unpack_from("<I", data, offset)[0],
                "format_id": format_id,
                "width": width,
                "height": height,
                "tagged_offset": tagged - 1,
            }
        )
    return descriptors


def locate_textures(data: bytes, block_sizes: list[int]) -> list[TextureRecord]:
    descriptors = scan_headers(data)
    header_offsets = {item["header_offset"] for item in descriptors}
    block_bases: list[int] = []
    cursor = 0
    for size in block_sizes:
        block_bases.append(cursor)
        cursor += size

    analyzed: list[dict[str, object]] = []
    for descriptor in descriptors:
        size = payload_size(
            descriptor["format_id"], descriptor["width"], descriptor["height"]
        )
        inline = descriptor["header_offset"] + HEADER_SIZE
        inline_end = inline + size
        overlaps_header = any(inline <= other < inline_end for other in header_offsets)
        inline_valid = inline_end <= len(data) and not overlaps_header

        metadata_block = 0
        for index, (base, block_size) in enumerate(zip(block_bases, block_sizes)):
            if base <= descriptor["header_offset"] < base + block_size:
                metadata_block = index
                break
        block_candidates: list[tuple[int, int]] = []
        for index, (base, block_size) in enumerate(zip(block_bases, block_sizes)):
            if index == metadata_block:
                continue
            local = descriptor["tagged_offset"]
            if local + size <= block_size:
                block_candidates.append((index, base + local))

        analyzed.append(
            {
                "descriptor": descriptor,
                "size": size,
                "inline": inline,
                "inline_valid": inline_valid,
                "metadata_block": metadata_block,
                "block_candidates": block_candidates,
            }
        )

    # Court/title IFFs keep a bank of adjacent descriptors in DRAM and all of
    # their payloads in the following VRAM block. The final descriptor alone
    # can look inline-valid, so classify the whole descriptor bank as split as
    # soon as one descriptor proves that layout.
    split_metadata_blocks = {
        int(item["metadata_block"])
        for item in analyzed
        if not item["inline_valid"] and item["block_candidates"]
    }
    block_payload_adjustments: dict[int, int] = {}
    for block_index, block_size in enumerate(block_sizes):
        block_items = [
            item
            for item in analyzed
            if int(item["metadata_block"]) in split_metadata_blocks
            and any(candidate[0] == block_index for candidate in item["block_candidates"])
        ]
        tagged_ends = [
            int(item["descriptor"]["tagged_offset"]) + int(item["size"])
            for item in block_items
        ]
        if tagged_ends:
            # Some UI IFFs (notably TITLEPAGE.IFF) place a small resource
            # prefix before tagged VRAM offset zero. When the tagged payload
            # bank otherwise lands exactly at the end of the block, account
            # for that prefix. Court VRAM has much larger unused regions and
            # correctly remains based at block offset zero. Large front-end
            # banks are adjusted only when a complete archive-specific hash
            # signature proves that their tags are end-relative.
            slack = block_size - max(tagged_ends)
            hashes = {
                int(item["descriptor"]["texture_hash"])
                for item in block_items
            }
            verified_end_anchored = any(
                signature.issubset(hashes)
                for signature in VERIFIED_END_ANCHORED_TEXTURE_BANKS
            )
            if 0 < slack and (slack <= 0x10000 or verified_end_anchored):
                block_payload_adjustments[block_index] = slack

    results: list[TextureRecord] = []
    for number, item in enumerate(analyzed, 1):
        descriptor = item["descriptor"]
        size = int(item["size"])
        inline = int(item["inline"])
        inline_valid = bool(item["inline_valid"])
        metadata_block = int(item["metadata_block"])
        block_candidates = item["block_candidates"]

        if metadata_block in split_metadata_blocks and block_candidates:
            preferred = next(
                (candidate for candidate in block_candidates if candidate[0] == metadata_block + 1),
                block_candidates[0],
            )
            adjustment = block_payload_adjustments.get(preferred[0], 0)
            payload_offset = preferred[1] + adjustment
            location = (
                f"block {preferred[0] + 1} + 0x{adjustment:X} resource base "
                f"+ 0x{descriptor['tagged_offset']:X}"
            )
            error = None
        elif inline_valid:
            payload_offset = inline
            location = "inline after VCTEXTURE header"
            error = None
        elif block_candidates:
            preferred = next(
                (item for item in block_candidates if item[0] == metadata_block + 1),
                block_candidates[0],
            )
            adjustment = block_payload_adjustments.get(preferred[0], 0)
            payload_offset = preferred[1] + adjustment
            location = (
                f"block {preferred[0] + 1} + 0x{adjustment:X} resource base "
                f"+ 0x{descriptor['tagged_offset']:X}"
            )
            error = None
        else:
            payload_offset = None
            location = "unresolved split DRAM/VRAM payload"
            error = (
                "Texture header found, but its payload block boundary is unknown. "
                "Re-extract this IFF with the updated OBB tool or open the original "
                "compressed IFF entry."
            )

        results.append(
            TextureRecord(
                number=number,
                header_offset=descriptor["header_offset"],
                texture_hash=descriptor["texture_hash"],
                format_id=descriptor["format_id"],
                width=descriptor["width"],
                height=descriptor["height"],
                tagged_offset=descriptor["tagged_offset"],
                payload_size=size,
                payload_offset=payload_offset,
                location=location,
                error=error,
            )
        )

    for texture in results:
        if texture.payload_offset is None:
            continue
        block_start, block_end = 0, len(data)
        for base, block_size in zip(block_bases, block_sizes):
            if base <= texture.payload_offset < base + block_size:
                block_start, block_end = base, base + block_size
                break
        limits = [block_end]
        limits.extend(
            other.header_offset
            for other in results
            if texture.payload_offset < other.header_offset < block_end
            and other.header_offset >= block_start
        )
        limits.extend(
            other.payload_offset
            for other in results
            if other.payload_offset is not None
            and texture.payload_offset < other.payload_offset < block_end
        )
        allocation_end = min(limits)
        inferred_size = allocation_end - texture.payload_offset
        # The descriptor's payload_size is authoritative for the base level.
        # Normally the payload must fit inside one decompressed wrapper block,
        # but some loading-screen IFFs intentionally split a large raw texture
        # across two adjacent compressed blocks. In that layout the old
        # block_end-only check reported only the remaining bytes in the first
        # block (e.g. 1832 bytes for a 2048x1024 RGB565 texture).
        base_size = texture.payload_size
        payload_end = texture.payload_offset + base_size
        can_span_blocks = payload_end <= len(data)
        if can_span_blocks:
            # Do not let a cross-block texture consume another texture's
            # descriptor/payload if one is actually serialized inside it.
            intervening = any(
                texture.payload_offset < marker < payload_end
                for other in results
                if other is not texture
                for marker in (
                    other.header_offset,
                    other.payload_offset if other.payload_offset is not None else -1,
                )
            )
            if not intervening:
                inferred_size = max(inferred_size, base_size)
        texture.allocation_size = inferred_size
        texture.allocation_size = inferred_size
        full_chain = mip_chain_size(texture.format_id, texture.width, texture.height)
        texture.uses_mip_chain = full_chain <= texture.allocation_size
        texture.encoded_size = full_chain if texture.uses_mip_chain else texture.payload_size
    return results


def reconcile_inline_texture_allocations(textures: list[TextureRecord]) -> None:
    """Prevent inferred inline mip chains from crossing later raw atlases.

    Uniform IFFs contain a descriptor-less RGBA8888 jersey atlas between the
    first and second inline texture payloads.  The inline-only scan cannot see
    that boundary and can therefore mistake the intervening serialized data
    for mip levels.  Reconcile allocations after every raw atlas has been
    detected so importing the name/letter atlas cannot overwrite the jersey
    atlas or the metadata immediately before it.
    """

    payload_starts = sorted(
        {
            texture.payload_offset
            for texture in textures
            if texture.payload_offset is not None
        }
    )
    for texture in textures:
        if not texture.has_header or texture.payload_offset is None:
            continue
        later_starts = [
            start for start in payload_starts if start > texture.payload_offset
        ]
        if not later_starts:
            continue
        safe_size = min(later_starts) - texture.payload_offset
        # Never shrink an allocation below the descriptor-declared base
        # payload.  The old reconciliation could turn a valid 4 MiB 2048x2048
        # ETC2 RGBA8 texture into a bogus 1 MiB allocation when another
        # texture happened to start inside the same inferred range.
        safe_size = max(safe_size, texture.payload_size)
        if texture.allocation_size and safe_size >= texture.allocation_size:
            continue
        texture.allocation_size = safe_size
        full_chain = mip_chain_size(texture.format_id, texture.width, texture.height)
        texture.uses_mip_chain = full_chain <= safe_size
        texture.encoded_size = (
            full_chain if texture.uses_mip_chain else texture.payload_size
        )


def rgba8888_candidate_metrics(payload: bytes) -> dict[str, float | int] | None:
    """Return measurable evidence that one exact byte range is an RGBA8888 image.

    Raw bytes alone cannot provide a mathematical format guarantee.  Requiring
    all five independent image properties avoids uniform.py's false-positive
    behavior while retaining every confirmed UH/UA atlas tested from the OBB.
    """

    expected = RAW_RGBA8888_PROBE_SIZE
    if len(payload) != expected:
        return None
    pixel_count = RAW_RGBA8888_PROBE_WIDTH * RAW_RGBA8888_PROBE_HEIGHT
    alpha = payload[3::4]
    alpha_counts = Counter(alpha)
    dominant_alpha, dominant_count = alpha_counts.most_common(1)[0]

    view = memoryview(payload)
    active_rgb = 0
    sampled_colors: set[tuple[int, int, int]] = set()
    neighbor_total = 0.0
    neighbor_count = 0
    sample_indices = range(0, pixel_count, 17)
    sample_count = len(sample_indices)
    for pixel in sample_indices:
        offset = pixel * 4
        rgb = (view[offset], view[offset + 1], view[offset + 2])
        sampled_colors.add(rgb)
        if rgb != (0, 0, 0):
            active_rgb += 1
        if pixel % RAW_RGBA8888_PROBE_WIDTH != RAW_RGBA8888_PROBE_WIDTH - 1:
            neighbor = offset + 4
            neighbor_total += (
                abs(view[offset] - view[neighbor])
                + abs(view[offset + 1] - view[neighbor + 1])
                + abs(view[offset + 2] - view[neighbor + 2])
            ) / 3
            neighbor_count += 1

    return {
        "dominant_alpha": dominant_alpha,
        "dominant_alpha_ratio": dominant_count / pixel_count,
        "alpha_unique": len(alpha_counts),
        "active_rgb_ratio": active_rgb / sample_count,
        "sampled_color_count": len(sampled_colors),
        "mean_horizontal_difference": neighbor_total / neighbor_count,
    }


def is_confident_rgba8888(metrics: dict[str, float | int] | None) -> bool:
    if metrics is None:
        return False
    return (
        metrics["dominant_alpha_ratio"] >= 0.50
        and metrics["alpha_unique"] <= 64
        and metrics["active_rgb_ratio"] >= 0.10
        and metrics["sampled_color_count"] >= 64
        and metrics["mean_horizontal_difference"] <= 20.0
    )


def is_confident_uniform_rgba8888(
    metrics: dict[str, float | int] | None,
) -> bool:
    """Validate the fixed visual atlas used by a known UH/UA uniform layout.

    Some uniforms use smooth or packed alpha values and legitimately exceed
    the generic detector's 64-value alpha limit.  The exact uniform texture
    signature already supplies strong structural evidence, so retain every
    other image-quality check while allowing the full 8-bit alpha range.
    """

    if metrics is None:
        return False
    return (
        metrics["dominant_alpha_ratio"] >= 0.50
        and metrics["alpha_unique"] <= 256
        and metrics["active_rgb_ratio"] >= 0.10
        and metrics["sampled_color_count"] >= 64
        and metrics["mean_horizontal_difference"] <= 20.0
    )


def _uniform_layout_signature(
    display_name: str, inline_textures: list[TextureRecord]
) -> bool:
    texture_signature = [
        (texture.texture_hash, texture.format_id, texture.width, texture.height)
        for texture in inline_textures[:3]
    ] == [
        (0xF2334940, 4, 1024, 64),
        (0x3E0620F6, 4, 1024, 128),
        (0x895C829E, 15, 512, 512),
    ]
    return bool(UNIFORM_IFF_NAME.match(display_name) or texture_signature)


def locate_detected_rgba8888_texture(
    data: bytes,
    block_sizes: list[int],
    display_name: str,
    inline_textures: list[TextureRecord],
    start_number: int,
) -> list[TextureRecord]:
    offset = RAW_RGBA8888_PROBE_OFFSET
    end = offset + RAW_RGBA8888_PROBE_SIZE
    containing_block = next(
        (
            (block_start, block_end)
            for block_start, block_end in _block_ranges(block_sizes)
            if block_start <= offset and end <= block_end
        ),
        None,
    )
    if containing_block is None or end > len(data):
        return []
    metrics = rgba8888_candidate_metrics(data[offset:end])
    is_uniform = _uniform_layout_signature(display_name, inline_textures)
    if not (
        is_confident_rgba8888(metrics)
        or (is_uniform and is_confident_uniform_rgba8888(metrics))
    ):
        return []
    assert metrics is not None
    label = (
        "Uniform Visual / Full Jersey Atlas"
        if is_uniform
        else "Detected Raw RGBA8888 Atlas"
    )
    evidence = (
        f"alpha 0x{int(metrics['dominant_alpha']):02X} "
        f"{float(metrics['dominant_alpha_ratio']):.1%}; "
        f"{int(metrics['alpha_unique'])} alpha values; "
        f"neighbor difference {float(metrics['mean_horizontal_difference']):.1f}"
    )
    return [
        TextureRecord(
            number=start_number,
            header_offset=offset,
            texture_hash=0,
            format_id=FORMAT_RGBA8888_RAW,
            width=RAW_RGBA8888_PROBE_WIDTH,
            height=RAW_RGBA8888_PROBE_HEIGHT,
            tagged_offset=offset - containing_block[0],
            payload_size=RAW_RGBA8888_PROBE_SIZE,
            payload_offset=offset,
            location=f"detected at decoded 0x{offset:X}; {evidence}",
            allocation_size=RAW_RGBA8888_PROBE_SIZE,
            encoded_size=RAW_RGBA8888_PROBE_SIZE,
            uses_mip_chain=False,
            label=label,
            has_header=False,
        )
    ]


def locate_uniform_streamed_textures(
    data: bytes,
    block_sizes: list[int],
    display_name: str,
    inline_textures: list[TextureRecord],
    start_number: int,
) -> list[TextureRecord]:
    """Expose the descriptor-less uniform visual, normal, and color atlases.

    UH###/UA### resources use a stable two-texture streamed block that is not
    described by the inline VCTEXTURE headers.  Treating the entire block as
    unknown data made the team chest wordmark impossible to edit.  Detection
    is deliberately restricted by both the uniform filename and exact block
    size so unrelated IFF payloads cannot be mislabeled or overwritten.
    """

    if not _uniform_layout_signature(display_name, inline_textures):
        return []
    if len(block_sizes) < 2:
        return []
    blocks = _block_ranges(block_sizes)
    block_start, block_end = blocks[-1]
    if block_end - block_start != UNIFORM_STREAM_BLOCK_SIZE:
        return []
    if block_end > len(data):
        return []

    normal_offset = block_start
    color_offset = block_start + UNIFORM_COLOR_STREAM_OFFSET
    if color_offset + UNIFORM_COLOR_STREAM_SIZE != block_end:
        return []

    return [
        TextureRecord(
            number=start_number,
            header_offset=normal_offset,
            texture_hash=0,
            format_id=4,
            width=512,
            height=512,
            tagged_offset=0,
            payload_size=payload_size(4, 512, 512),
            payload_offset=normal_offset,
            location="streamed uniform block + 0x0",
            allocation_size=UNIFORM_NORMAL_STREAM_SIZE,
            encoded_size=UNIFORM_NORMAL_ENCODED_SIZE,
            uses_mip_chain=True,
            label="Uniform Normal / Chest Wordmark Atlas",
            has_header=False,
        ),
        TextureRecord(
            number=start_number + 1,
            header_offset=color_offset,
            texture_hash=0,
            format_id=15,
            width=512,
            height=512,
            tagged_offset=UNIFORM_COLOR_STREAM_OFFSET,
            payload_size=payload_size(15, 512, 512),
            payload_offset=color_offset,
            location=f"streamed uniform block + 0x{UNIFORM_COLOR_STREAM_OFFSET:X}",
            allocation_size=UNIFORM_COLOR_STREAM_SIZE,
            encoded_size=UNIFORM_COLOR_STREAM_SIZE,
            uses_mip_chain=True,
            label="Uniform Color / Team Logo Atlas",
            has_header=False,
        ),
    ]


def _block_ranges(block_sizes: list[int]) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    start = 0
    for size in block_sizes:
        ranges.append((start, start + size))
        start += size
    return ranges


def _range_overlaps(
    start: int, end: int, ranges: list[tuple[int, int]]
) -> bool:
    return any(start < other_end and other_start < end for other_start, other_end in ranges)


def _ogg_page(
    data: bytes, offset: int, block_end: int
) -> tuple[int, int, int] | None:
    if offset + 27 > block_end or data[offset : offset + 4] != b"OggS":
        return None
    if data[offset + 4] != 0:
        return None
    segment_count = data[offset + 26]
    header_end = offset + 27 + segment_count
    if header_end > block_end:
        return None
    body_size = sum(data[offset + 27 : header_end])
    page_end = header_end + body_size
    if page_end > block_end:
        return None
    serial = struct.unpack_from("<I", data, offset + 14)[0]
    return page_end, serial, data[offset + 5]


def _find_ogg_streams(
    data: bytes, block_start: int, block_end: int
) -> list[tuple[int, int, str]]:
    streams: list[tuple[int, int, str]] = []
    search = block_start
    while True:
        start = data.find(b"OggS", search, block_end)
        if start < 0:
            break
        first = _ogg_page(data, start, block_end)
        if first is None or not (first[2] & 0x02):
            search = start + 4
            continue
        position = start
        page_count = 0
        serial = first[1]
        saw_eos = False
        while True:
            page = _ogg_page(data, position, block_end)
            if page is None or page[1] != serial:
                break
            page_count += 1
            position = page[0]
            if page[2] & 0x04:
                saw_eos = True
                break
        if page_count and (saw_eos or page_count > 1):
            state = "complete" if saw_eos else "no EOS page"
            streams.append(
                (
                    start,
                    position,
                    f"Ogg serial 0x{serial:08X}; {page_count} page(s); {state}",
                )
            )
            search = position
        else:
            search = start + 4
    return streams


def _find_png_end(data: bytes, start: int, block_end: int) -> int | None:
    position = start + 8
    while position + 12 <= block_end:
        length = struct.unpack_from(">I", data, position)[0]
        chunk_end = position + 12 + length
        if chunk_end > block_end:
            return None
        chunk_type = data[position + 4 : position + 8]
        position = chunk_end
        if chunk_type == b"IEND":
            return position
    return None


def _find_jpeg_end(data: bytes, start: int, block_end: int) -> int | None:
    """Validate JPEG marker structure and return the exact EOI boundary."""

    if start + 4 > block_end or data[start : start + 2] != b"\xFF\xD8":
        return None
    position = start + 2
    in_scan = False
    while position < block_end:
        if in_scan:
            marker_start = data.find(b"\xFF", position, block_end)
            if marker_start < 0:
                return None
        else:
            marker_start = position
            if data[marker_start] != 0xFF:
                return None
        position = marker_start + 1
        while position < block_end and data[position] == 0xFF:
            position += 1
        if position >= block_end:
            return None
        marker = data[position]
        position += 1
        if marker == 0x00:  # Byte-stuffed 0xFF within entropy-coded data.
            if not in_scan:
                return None
            continue
        if marker == 0xD9:  # EOI
            return position
        if marker == 0xD8:  # Nested SOI is not a valid continuation.
            return None
        if marker == 0x01 or 0xD0 <= marker <= 0xD7:
            if not in_scan:
                return None
            continue
        # Remaining JPEG segments carry a big-endian length that includes the
        # two length bytes themselves.
        if position + 2 > block_end:
            return None
        segment_size = struct.unpack_from(">H", data, position)[0]
        if segment_size < 2 or position + segment_size > block_end:
            return None
        position += segment_size
        in_scan = marker == 0xDA  # Start Of Scan
    return None


def locate_gpu_buffers(
    data: bytes, block_sizes: list[int], textures: list[TextureRecord]
) -> list[GpuBufferRecord]:
    """Find shared 2K GPU-buffer descriptors without assuming one model name.

    A common descriptor stores stride, byte size, and a tagged local offset.
    The detector is intentionally conservative and records a score so future
    layout-specific mesh parsers can build on the same folder-wide inventory.
    """

    if len(block_sizes) < 2:
        return []
    blocks = _block_ranges(block_sizes)
    metadata_end = blocks[0][1]
    stride_values = bytes(range(12, 129, 4))
    stride_pattern = re.compile(b"[" + re.escape(stride_values) + b"]\x00\x00\x00")
    texture_ranges = [
        (texture.payload_offset, texture.payload_offset + (texture.encoded_size or texture.payload_size))
        for texture in textures
        if texture.payload_offset is not None
    ]
    candidates: list[GpuBufferRecord] = []
    seen: set[tuple[int, int, int, int]] = set()
    for match in stride_pattern.finditer(data, 0, metadata_end):
        offset = match.start()
        if offset % 4 or offset + 12 > metadata_end:
            continue
        stride, size, tagged = struct.unpack_from("<III", data, offset)
        if stride < 12 or stride > 128 or stride % 4:
            continue
        if size < stride * 3 or size % stride or tagged < 1 or not (tagged & 1):
            continue
        local = tagged - 1
        element_count = size // stride
        if element_count > 4_000_000:
            continue
        for block_index, (block_start, block_end) in enumerate(blocks[1:], 1):
            block_size = block_end - block_start
            if local + size > block_size:
                continue
            payload_offset = block_start + local
            payload_end = payload_offset + size
            if _range_overlaps(payload_offset, payload_end, texture_ranges):
                continue
            sample = data[payload_offset : min(payload_end, payload_offset + 4096)]
            if not sample or not any(sample):
                continue
            score = 20
            if local % 16 == 0:
                score += 10
            if size % 16 == 0:
                score += 5
            if local + size == block_size:
                score += 50
            elif block_size - (local + size) <= 256:
                score += 20
            # Float-based vertex streams are common. Finite first attributes
            # raise confidence, while packed formats remain valid candidates.
            finite = 0
            checked = 0
            for item in range(min(element_count, 32)):
                start = payload_offset + item * stride
                try:
                    values = struct.unpack_from("<3f", data, start)
                except struct.error:
                    break
                checked += 1
                if all(value == value and abs(value) < 1_000_000 for value in values):
                    finite += 1
            if checked and finite == checked:
                score += 15
            key = (block_index, local, size, stride)
            if key in seen:
                continue
            seen.add(key)
            candidates.append(
                GpuBufferRecord(
                    number=0,
                    metadata_offset=offset,
                    block_index=block_index,
                    local_offset=local,
                    payload_offset=payload_offset,
                    size=size,
                    stride=stride,
                    element_count=element_count,
                    score=score,
                )
            )
    candidates.sort(key=lambda item: (-item.score, item.payload_offset, item.stride))
    for number, candidate in enumerate(candidates, 1):
        candidate.number = number
    return candidates


def mesh_positions(opened: OpenedIff, mesh: MeshRecord) -> list[tuple[float, float, float]]:
    """Decode the validated float32 XYZ stream for a mesh."""

    return [
        struct.unpack_from(
            "<3f",
            opened.data,
            mesh.vertex_offset + index * mesh.vertex_stride + mesh.position_offset,
        )
        for index in range(mesh.vertex_count)
    ]


def mesh_indices(opened: OpenedIff, mesh: MeshRecord) -> tuple[int, ...]:
    return struct.unpack_from(
        f"<{mesh.index_count}H", opened.data, mesh.index_offset
    )


def triangle_strip_faces(indices: tuple[int, ...] | list[int]) -> list[tuple[int, int, int]]:
    """Convert a 2K/OpenGL triangle strip, including degenerate joins, to faces."""

    faces: list[tuple[int, int, int]] = []
    for position in range(len(indices) - 2):
        first, second, third = indices[position : position + 3]
        if position & 1:
            first, second = second, first
        if 0xFFFF in (first, second, third):
            continue
        if first == second or second == third or first == third:
            continue
        faces.append((first, second, third))
    return faces


def _candidate_index_prefix(
    data: bytes, block_start: int, local_offset: int, vertex_count: int
) -> tuple[int, tuple[int, ...]] | None:
    """Validate the index stream stored before a single interleaved vertex stream."""

    if local_offset < 6 or local_offset > 32 * 1024 * 1024:
        return None
    effective_size = local_offset
    while effective_size and data[block_start + effective_size - 1] == 0:
        effective_size -= 1
    effective_size += effective_size % 2
    if effective_size < 6 or local_offset - effective_size > 512:
        return None
    values = struct.unpack_from(f"<{effective_size // 2}H", data, block_start)
    if not values or any(value >= vertex_count and value != 0xFFFF for value in values):
        return None
    if max((value for value in values if value != 0xFFFF), default=0) < vertex_count // 4:
        return None
    return effective_size, values


def locate_meshes(
    data: bytes, block_sizes: list[int], gpu_buffers: list[GpuBufferRecord]
) -> list[MeshRecord]:
    """Decode only high-confidence model streams whose layout is proven by data.

    The supported family stores float32 XYZ at the start of an interleaved
    vertex record and a validated uint16 triangle strip before it. Packed and
    shared-stream families remain in the generic GPU-buffer list until their
    position declarations can be decoded without guessing.
    """

    blocks = _block_ranges(block_sizes)
    meshes: list[MeshRecord] = []
    seen: set[tuple[int, int]] = set()
    for buffer in gpu_buffers:
        if buffer.stride < 12 or buffer.element_count < 4 or buffer.score < 45:
            continue
        key = (buffer.payload_offset, buffer.size)
        if key in seen:
            continue
        seen.add(key)
        sample_step = max(1, buffer.element_count // 256)
        sampled: list[tuple[float, float, float]] = []
        sample_valid = True
        for vertex in range(0, buffer.element_count, sample_step):
            values = struct.unpack_from(
                "<3f", data, buffer.payload_offset + vertex * buffer.stride
            )
            if not all(math.isfinite(value) and abs(value) < 1_000_000 for value in values):
                sample_valid = False
                break
            sampled.append(values)
            if len(sampled) == 256:
                break
        if not sample_valid or not sampled:
            continue
        unit_ratio = sum(
            0.995 <= math.sqrt(x * x + y * y + z * z) <= 1.005
            for x, y, z in sampled
        ) / len(sampled)
        if unit_ratio >= 0.95:
            continue
        block_start, _block_end = blocks[buffer.block_index]
        index_result = _candidate_index_prefix(
            data, block_start, buffer.local_offset, buffer.element_count
        )
        if index_result is None:
            continue
        index_size, indices = index_result

        positions: list[tuple[float, float, float]] = []
        valid_positions = True
        for vertex in range(buffer.element_count):
            values = struct.unpack_from(
                "<3f", data, buffer.payload_offset + vertex * buffer.stride
            )
            if not all(math.isfinite(value) and abs(value) < 1_000_000 for value in values):
                valid_positions = False
                break
            positions.append(values)
        if not valid_positions:
            continue

        bounds = [
            (min(point[axis] for point in positions), max(point[axis] for point in positions))
            for axis in range(3)
        ]
        diagonal = math.sqrt(sum((high - low) ** 2 for low, high in bounds))
        if diagonal <= 1e-6 or sum(high - low > diagonal * 1e-5 for low, high in bounds) < 2:
            continue

        # Normal/tangent-only streams often begin with unit vectors. Do not
        # mislabel those as positions even when their bytes are valid floats.
        faces = triangle_strip_faces(indices)
        if not faces or any(max(face) >= len(positions) for face in faces):
            continue
        nondegenerate: list[tuple[int, int, int]] = []
        edge_lengths: list[float] = []
        for face in faces:
            first, second, third = (positions[index] for index in face)
            ab = tuple(second[axis] - first[axis] for axis in range(3))
            ac = tuple(third[axis] - first[axis] for axis in range(3))
            cross = (
                ab[1] * ac[2] - ab[2] * ac[1],
                ab[2] * ac[0] - ab[0] * ac[2],
                ab[0] * ac[1] - ab[1] * ac[0],
            )
            area2 = math.sqrt(sum(value * value for value in cross))
            if area2 <= diagonal * diagonal * 1e-12:
                continue
            nondegenerate.append(face)
            edge_lengths.extend(
                (
                    math.dist(first, second),
                    math.dist(second, third),
                    math.dist(third, first),
                )
            )
        if len(nondegenerate) < max(4, buffer.element_count // 10):
            continue
        edge_lengths.sort()
        edge_p95 = edge_lengths[min(len(edge_lengths) - 1, int(len(edge_lengths) * 0.95))]
        if edge_p95 / diagonal > 0.35:
            continue

        bounds_text = ", ".join(
            f"{axis} {low:.3g}..{high:.3g}"
            for axis, (low, high) in zip("XYZ", bounds)
        )
        meshes.append(
            MeshRecord(
                number=0,
                buffer_number=buffer.number,
                vertex_offset=buffer.payload_offset,
                vertex_stride=buffer.stride,
                vertex_count=buffer.element_count,
                position_offset=0,
                index_offset=block_start,
                index_count=index_size // 2,
                triangle_count=len(nondegenerate),
                topology="triangle strip",
                confidence="validated float32 XYZ + uint16 strip",
                details=f"{bounds_text}; GPU descriptor 0x{buffer.metadata_offset:X}",
            )
        )
    meshes.sort(key=lambda item: (item.vertex_offset, item.vertex_stride))
    for number, mesh in enumerate(meshes, 1):
        mesh.number = number
    return meshes


def mesh_faces(opened: OpenedIff, mesh: MeshRecord) -> list[tuple[int, int, int]]:
    positions = mesh_positions(opened, mesh)
    faces = triangle_strip_faces(mesh_indices(opened, mesh))
    diagonal = math.dist(
        tuple(min(point[axis] for point in positions) for axis in range(3)),
        tuple(max(point[axis] for point in positions) for axis in range(3)),
    )
    result: list[tuple[int, int, int]] = []
    for face in faces:
        if max(face) >= len(positions):
            continue
        first, second, third = (positions[index] for index in face)
        ab = tuple(second[axis] - first[axis] for axis in range(3))
        ac = tuple(third[axis] - first[axis] for axis in range(3))
        cross = (
            ab[1] * ac[2] - ab[2] * ac[1],
            ab[2] * ac[0] - ab[0] * ac[2],
            ab[0] * ac[1] - ab[1] * ac[0],
        )
        if math.sqrt(sum(value * value for value in cross)) > diagonal * diagonal * 1e-12:
            result.append(face)
    return result


def export_mesh_obj(opened: OpenedIff, mesh: MeshRecord, destination: Path) -> None:
    """Export a validated mesh as a standards-compatible Wavefront OBJ."""

    positions = mesh_positions(opened, mesh)
    faces = mesh_faces(opened, mesh)
    lines = [
        "# NBA 2K20 Android IFF Resource Manager",
        f"# source: {opened.path.name}",
        f"# layout: {mesh.confidence}",
        f"o {opened.path.stem}_mesh_{mesh.number:03d}",
    ]
    lines.extend(f"v {x:.9g} {y:.9g} {z:.9g}" for x, y, z in positions)
    lines.extend(f"f {first + 1} {second + 1} {third + 1}" for first, second, third in faces)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines) + "\n", encoding="utf-8")


def import_mesh_obj(
    opened: OpenedIff, mesh: MeshRecord, source: Path
) -> dict[str, object]:
    """Import only OBJ vertex positions while preserving the 2K vertex layout."""

    positions: list[tuple[float, float, float]] = []
    with source.open("r", encoding="utf-8-sig", errors="replace") as handle:
        for line_number, line in enumerate(handle, 1):
            stripped = line.lstrip()
            if not stripped.startswith("v "):
                continue
            fields = stripped.split()
            if len(fields) < 4:
                raise ValueError(f"invalid OBJ vertex on line {line_number}")
            try:
                vertex = tuple(float(value) for value in fields[1:4])
            except ValueError as error:
                raise ValueError(f"invalid OBJ vertex on line {line_number}") from error
            if not all(math.isfinite(value) and abs(value) < 1_000_000 for value in vertex):
                raise ValueError(
                    f"OBJ vertex on line {line_number} is non-finite or outside the safe range"
                )
            positions.append(vertex)
    if len(positions) != mesh.vertex_count:
        raise ValueError(
            f"OBJ has {len(positions):,} vertex position(s); this IFF mesh requires "
            f"exactly {mesh.vertex_count:,}. Do not add, delete, merge, sort, or reorder vertices."
        )
    original = bytes(
        opened.data[mesh.vertex_offset : mesh.vertex_offset + mesh.vertex_stride * mesh.vertex_count]
    )
    for index, position in enumerate(positions):
        struct.pack_into(
            "<3f",
            opened.data,
            mesh.vertex_offset + index * mesh.vertex_stride + mesh.position_offset,
            *position,
        )
    changed = sum(
        before != after
        for before, after in zip(
            original,
            opened.data[
                mesh.vertex_offset : mesh.vertex_offset
                + mesh.vertex_stride * mesh.vertex_count
            ],
        )
    )
    return {
        "kind": "3D mesh positions",
        "mesh_number": mesh.number,
        "source": str(source.resolve()),
        "vertex_count": mesh.vertex_count,
        "changed_bytes": changed,
        "preserved": "normals/tangents, UVs, skin weights, bone indices, and topology",
    }


def mesh_wireframe_image(
    opened: OpenedIff, mesh: MeshRecord, size: tuple[int, int] = (820, 590)
) -> Image.Image:
    """Render a dependency-free isometric wireframe for the GUI preview."""

    positions = mesh_positions(opened, mesh)
    faces = mesh_faces(opened, mesh)
    center = tuple(
        (min(point[axis] for point in positions) + max(point[axis] for point in positions)) / 2
        for axis in range(3)
    )
    yaw = math.radians(-28)
    pitch = math.radians(12)
    transformed: list[tuple[float, float, float]] = []
    for x, y, z in positions:
        x -= center[0]
        y -= center[1]
        z -= center[2]
        rotated_x = x * math.cos(yaw) + z * math.sin(yaw)
        rotated_z = -x * math.sin(yaw) + z * math.cos(yaw)
        rotated_y = y * math.cos(pitch) - rotated_z * math.sin(pitch)
        depth = y * math.sin(pitch) + rotated_z * math.cos(pitch)
        transformed.append((rotated_x, rotated_y, depth))
    low_x, high_x = min(p[0] for p in transformed), max(p[0] for p in transformed)
    low_y, high_y = min(p[1] for p in transformed), max(p[1] for p in transformed)
    width, height = size
    scale = min(
        (width - 56) / max(high_x - low_x, 1e-9),
        (height - 76) / max(high_y - low_y, 1e-9),
    )
    offset_x = width / 2 - (low_x + high_x) * scale / 2
    offset_y = height / 2 + (low_y + high_y) * scale / 2
    projected = [
        (x * scale + offset_x, -y * scale + offset_y, depth)
        for x, y, depth in transformed
    ]
    image = Image.new("RGB", size, "#17191D")
    draw = ImageDraw.Draw(image)
    edges: set[tuple[int, int]] = set()
    for first, second, third in faces:
        edges.update(
            (
                tuple(sorted((first, second))),
                tuple(sorted((second, third))),
                tuple(sorted((third, first))),
            )
        )
    for first, second in sorted(
        edges, key=lambda edge: (projected[edge[0]][2] + projected[edge[1]][2]) / 2
    ):
        draw.line(
            (projected[first][0:2], projected[second][0:2]),
            fill="#A7D8FF",
            width=1,
        )
    draw.text(
        (14, 12),
        f"Mesh {mesh.number}  |  {mesh.vertex_count:,} vertices  |  "
        f"{mesh.triangle_count:,} triangles",
        fill="#FFFFFF",
    )
    draw.text((14, height - 28), "Validated wireframe preview · OBJ export available", fill="#8FA5B8")
    return image


def _meaningful_text(value: str) -> bool:
    if len(value) < 8 or not re.search(r"[A-Za-z]{3}", value):
        return False
    useful = sum(character.isalnum() or character in " _-./:[]()#" for character in value)
    return useful / len(value) >= 0.65


def locate_resources(
    data: bytes,
    block_sizes: list[int],
    textures: list[TextureRecord],
    gpu_buffers: list[GpuBufferRecord],
) -> list[ResourceRecord]:
    """Expose every block and classify every byte range we can identify.

    The top-level block rows cover the complete IFF. Child rows identify known
    embedded resources. Complements are retained as unclassified binary ranges,
    which is preferable to inventing filenames for undocumented 2K objects.
    """

    blocks = _block_ranges(block_sizes)
    containers: list[ResourceRecord] = []
    leaf: list[ResourceRecord] = []
    covered: list[tuple[int, int]] = []
    covered_starts: list[int] = []

    def overlaps_covered(start: int, end: int) -> bool:
        index = bisect.bisect_left(covered_starts, start)
        if index and covered[index - 1][1] > start:
            return True
        return index < len(covered) and covered[index][0] < end

    def remember_covered(start: int, end: int) -> None:
        index = bisect.bisect_left(covered_starts, start)
        covered_starts.insert(index, start)
        covered.insert(index, (start, end))

    for index, (start, end) in enumerate(blocks, 1):
        if len(blocks) == 1:
            name = "IFF data block"
            details = "Complete decompressed IFF data"
        elif index == 1:
            name = "DRAM / metadata block"
            details = "First decompressed block; commonly metadata and descriptors"
        else:
            name = f"VRAM / data block {index}"
            details = "Decompressed data block; commonly GPU payload or streamed data"
        containers.append(
            ResourceRecord(
                number=0,
                kind="Container block",
                name=name,
                offset=start,
                size=end - start,
                extension=".bin",
                details=details,
                container=True,
            )
        )

    def add_leaf(
        kind: str,
        name: str,
        start: int,
        end: int,
        extension: str,
        details: str,
        *,
        confidence: str = "signature",
        texture_number: int | None = None,
        allow_overlap: bool = False,
    ) -> bool:
        if start < 0 or end <= start or end > len(data):
            return False
        if not allow_overlap and overlaps_covered(start, end):
            return False
        leaf.append(
            ResourceRecord(
                number=0,
                kind=kind,
                name=name,
                offset=start,
                size=end - start,
                extension=extension,
                details=details,
                confidence=confidence,
                texture_number=texture_number,
            )
        )
        remember_covered(start, end)
        return True

    for texture in textures:
        if texture.has_header:
            add_leaf(
                "Texture header",
                f"Texture {texture.number:03d} descriptor",
                texture.header_offset,
                texture.header_offset + HEADER_SIZE,
                ".bin",
                (
                    f"hash 0x{texture.texture_hash:08X}; {texture.width}x{texture.height}; "
                    f"{FORMAT_NAMES[texture.format_id]}"
                ),
                confidence="exact",
                texture_number=texture.number,
            )
        if texture.payload_offset is not None:
            encoded_size = texture.encoded_size or texture.payload_size
            add_leaf(
                "Streamed texture payload" if not texture.has_header else "Texture payload",
                texture.label or f"Texture {texture.number:03d} GPU payload",
                texture.payload_offset,
                texture.payload_offset + encoded_size,
                ".gpu",
                (
                    f"{texture.width}x{texture.height}; {FORMAT_NAMES[texture.format_id]}; "
                    + ("full mip chain" if texture.uses_mip_chain else "base level")
                ),
                confidence=(
                    "RGBA8888 structural/statistical detection"
                    if texture.format_id == FORMAT_RGBA8888_RAW
                    else (
                        "verified UH/UA uniform stream layout"
                        if not texture.has_header
                        else "exact"
                    )
                ),
                texture_number=texture.number,
                allow_overlap=texture.format_id == FORMAT_RGBA8888_RAW,
            )

    accepted_buffers: list[GpuBufferRecord] = []
    for buffer in gpu_buffers:
        accepted = add_leaf(
            "GPU vertex/data buffer",
            f"GPU buffer {buffer.number:03d}",
            buffer.payload_offset,
            buffer.payload_offset + buffer.size,
            ".vbuf",
            (
                f"stride {buffer.stride}; {buffer.element_count:,} element(s); "
                f"descriptor 0x{buffer.metadata_offset:X}; heuristic score {buffer.score}"
            ),
            confidence="2K GPU descriptor",
        )
        if accepted:
            accepted_buffers.append(buffer)

    for buffer in accepted_buffers:
        block_start, _block_end = blocks[buffer.block_index]
        if buffer.local_offset < 6 or buffer.local_offset > 16 * 1024 * 1024:
            continue
        effective_size = buffer.local_offset
        while effective_size and data[block_start + effective_size - 1] == 0:
            effective_size -= 1
        effective_size += effective_size % 2
        if effective_size < 6:
            continue
        value_count = effective_size // 2
        sample_count = min(value_count, 32_768)
        valid = 0
        for sample_index in range(sample_count):
            value_index = sample_index * value_count // sample_count
            value = struct.unpack_from(
                "<H", data, block_start + value_index * 2
            )[0]
            if value < buffer.element_count or value == 0xFFFF:
                valid += 1
        if sample_count and valid / sample_count >= 0.98:
            validation_note = (
                "all indices validated"
                if sample_count == value_count
                else f"{sample_count:,} evenly sampled indices validated"
            )
            add_leaf(
                "GPU index buffer",
                f"Index buffer for GPU buffer {buffer.number:03d}",
                block_start,
                block_start + effective_size,
                ".ibuf",
                (
                    f"{value_count:,} unsigned 16-bit indices; "
                    f"vertex/data elements {buffer.element_count:,}; "
                    f"{validation_note}"
                ),
                confidence="validated 16-bit index layout",
            )

    embedded_counts: dict[str, int] = {}

    def embedded_name(label: str, extension: str) -> str:
        embedded_counts[label] = embedded_counts.get(label, 0) + 1
        return f"{label} {embedded_counts[label]:03d}{extension}"

    for block_start, block_end in blocks:
        # Standard files whose own headers provide an exact end.
        position = block_start
        while True:
            position = data.find(b"\x89PNG\r\n\x1a\n", position, block_end)
            if position < 0:
                break
            end = _find_png_end(data, position, block_end)
            if end is not None:
                add_leaf(
                    "Embedded image",
                    embedded_name("PNG image", ".png"),
                    position,
                    end,
                    ".png",
                    "Complete PNG stream",
                )
            position += 8

        position = block_start
        while True:
            position = data.find(b"RIFF", position, block_end)
            if position < 0:
                break
            if position + 12 <= block_end:
                end = position + 8 + struct.unpack_from("<I", data, position + 4)[0]
                form = data[position + 8 : position + 12]
                if end <= block_end and form in (b"WAVE", b"AVI ", b"WEBP"):
                    extension = {b"WAVE": ".wav", b"AVI ": ".avi", b"WEBP": ".webp"}[form]
                    add_leaf(
                        "Embedded RIFF",
                        embedded_name(form.decode("ascii").strip() or "RIFF", extension),
                        position,
                        end,
                        extension,
                        f"RIFF form {form.decode('ascii', errors='replace')}",
                    )
            position += 4

        for start, end, details in _find_ogg_streams(data, block_start, block_end):
            add_leaf(
                "Embedded audio",
                embedded_name("Ogg Vorbis audio", ".ogg"),
                start,
                end,
                ".ogg",
                details,
            )

        position = block_start
        while True:
            position = data.find(b"\xFF\xD8\xFF", position, block_end)
            if position < 0:
                break
            end_marker = _find_jpeg_end(data, position, block_end)
            valid_jpeg = False
            if end_marker is not None and end_marker - position >= 128:
                candidate = data[position:end_marker]
                try:
                    with Image.open(io.BytesIO(candidate)) as embedded:
                        valid_jpeg = embedded.format == "JPEG"
                        embedded.verify()
                except Exception:  # noqa: BLE001 - reject binary lookalikes
                    valid_jpeg = False
            if valid_jpeg:
                add_leaf(
                    "Embedded image",
                    embedded_name("JPEG image", ".jpg"),
                    position,
                    end_marker,
                    ".jpg",
                    "Complete JPEG stream",
                )
            position += 3

        # 2K stores many compiled-material shader sources as null-terminated
        # GLSL text. Requiring both a newline and void main avoids random hits.
        position = block_start
        while True:
            position = data.find(b"#version ", position, block_end)
            if position < 0:
                break
            maximum = min(block_end, position + 2 * 1024 * 1024)
            terminator = data.find(b"\x00", position, maximum)
            if terminator > position:
                source = data[position:terminator]
                if b"\n" in source and b"void main" in source:
                    first_line = source.splitlines()[0].decode("ascii", errors="replace")
                    add_leaf(
                        "Shader source",
                        embedded_name("GLSL shader", ".glsl"),
                        position,
                        terminator,
                        ".glsl",
                        first_line,
                    )
            position += 9

        position = block_start
        while True:
            position = data.find(b"<?xml", position, block_end)
            if position < 0:
                break
            maximum = min(block_end, position + 8 * 1024 * 1024)
            terminator = data.find(b"\x00", position, maximum)
            close = data.rfind(b">", position, terminator if terminator >= 0 else maximum)
            if close >= position:
                add_leaf(
                    "XML text",
                    embedded_name("XML document", ".xml"),
                    position,
                    close + 1,
                    ".xml",
                    "Null-terminated XML text",
                )
            position += 5

    # Human-readable identifiers, paths, table labels, and names are useful
    # editable resources even when the surrounding object schema is unknown.
    # A per-IFF cap prevents pathological databases while preserving all bytes
    # through the later unclassified coverage rows.
    text_count = 0
    text_limit = 2000
    text_patterns = (
        ("ascii", re.compile(rb"[\x20-\x7e]{8,}\x00")),
        ("utf-16le", re.compile(rb"(?:[\x20-\x7e]\x00){8,}\x00\x00")),
    )
    for encoding, pattern in text_patterns:
        for match in pattern.finditer(data):
            if text_count >= text_limit:
                break
            start, end = match.span()
            if overlaps_covered(start, end):
                continue
            terminator = 1 if encoding == "ascii" else 2
            try:
                value = data[start : end - terminator].decode(encoding)
            except UnicodeDecodeError:
                continue
            if not _meaningful_text(value):
                continue
            text_count += 1
            excerpt = value[:100].replace("\r", " ").replace("\n", " ")
            add_leaf(
                "Text string",
                f"Text string {text_count:04d}",
                start,
                end,
                ".txt",
                f"{encoding}: {excerpt}",
                confidence="printable null-terminated text",
            )

    # The child list accounts for every byte. Gaps are not claimed to be
    # separate named files; they are exportable raw regions for further study.
    known = covered
    unknown_index = 0
    for block_index, (block_start, block_end) in enumerate(blocks, 1):
        cursor = block_start
        for start, end in known:
            if end <= block_start or start >= block_end:
                continue
            start = max(start, block_start)
            end = min(end, block_end)
            if cursor < start:
                unknown_index += 1
                leaf.append(
                    ResourceRecord(
                        number=0,
                        kind="Unclassified binary",
                        name=f"Unclassified region {unknown_index:03d}",
                        offset=cursor,
                        size=start - cursor,
                        extension=".bin",
                        details=f"Undocumented serialized data in block {block_index}",
                        confidence="byte coverage",
                    )
                )
            cursor = max(cursor, end)
        if cursor < block_end:
            unknown_index += 1
            leaf.append(
                ResourceRecord(
                    number=0,
                    kind="Unclassified binary",
                    name=f"Unclassified region {unknown_index:03d}",
                    offset=cursor,
                    size=block_end - cursor,
                    extension=".bin",
                    details=f"Undocumented serialized data in block {block_index}",
                    confidence="byte coverage",
                )
            )

    resources = containers + sorted(leaf, key=lambda item: (item.offset, item.size, item.kind))
    for number, resource in enumerate(resources, 1):
        resource.number = number
    return resources


def open_iff_bytes(
    raw: bytes,
    display_path: Path,
    *,
    look_for_manifest: bool = False,
) -> OpenedIff:
    """Parse an IFF from bytes, including an entry read directly from an OBB."""

    path = display_path.resolve()
    if not raw:
        raise ValueError("IFF file is empty")
    data, block_sizes, wrapper, wrapper_info = decompress_wrapper(raw)
    boundary_source = "compressed wrapper"
    if wrapper == "decompressed IFF":
        recorded = None
        if look_for_manifest:
            recorded, boundary_source = find_recorded_block_sizes(path, len(data))
        else:
            boundary_source = "not recorded"
        if recorded:
            block_sizes = recorded
        else:
            boundary_source = (
                "single block / no companion manifest"
                if boundary_source == "not recorded"
                else boundary_source
            )
    textures = locate_textures(data, block_sizes)
    inline_textures = list(textures)
    textures.extend(
        locate_detected_rgba8888_texture(
            data,
            block_sizes,
            display_path.name,
            inline_textures,
            len(textures) + 1,
        )
    )
    textures.extend(
        locate_uniform_streamed_textures(
            data,
            block_sizes,
            display_path.name,
            inline_textures,
            len(textures) + 1,
        )
    )
    reconcile_inline_texture_allocations(textures)

    # GPU/model/resource discovery can be very expensive for large IFFs,
    # especially under pure Python on Android.  Do not pay that cost just to
    # open a texture-editing file.  The UI loads these inventories lazily.
    gpu_buffers: list[GpuBufferRecord] = []
    meshes: list[MeshRecord] = []
    resources: list[ResourceRecord] = []
    return OpenedIff(
        path=path,
        source_size=len(raw),
        wrapper=wrapper,
        source_raw=raw,
        original_data=data,
        data=bytearray(data),
        block_sizes=block_sizes,
        boundary_source=boundary_source,
        textures=textures,
        gpu_buffers=gpu_buffers,
        meshes=meshes,
        resources=resources,
        wrapper_info=wrapper_info,
    )


def open_iff(path: Path) -> OpenedIff:
    path = path.resolve()
    if not path.is_file():
        raise ValueError(f"IFF file was not found: {path}")
    return open_iff_bytes(path.read_bytes(), path, look_for_manifest=True)


def decode_rgb565(payload: bytes, width: int, height: int) -> Image.Image:
    output = bytearray(width * height * 4)
    for index, (pixel,) in enumerate(struct.iter_unpack("<H", payload)):
        red = (pixel >> 11) & 0x1F
        green = (pixel >> 5) & 0x3F
        blue = pixel & 0x1F
        start = index * 4
        output[start : start + 4] = bytes(
            ((red << 3) | (red >> 2), (green << 2) | (green >> 4), (blue << 3) | (blue >> 2), 255)
        )
    return Image.frombytes("RGBA", (width, height), bytes(output))


def decode_rgba4444(payload: bytes, width: int, height: int) -> Image.Image:
    output = bytearray(width * height * 4)
    for index, (pixel,) in enumerate(struct.iter_unpack("<H", payload)):
        start = index * 4
        output[start : start + 4] = bytes(
            (
                ((pixel >> 12) & 0xF) * 17,
                ((pixel >> 8) & 0xF) * 17,
                ((pixel >> 4) & 0xF) * 17,
                (pixel & 0xF) * 17,
            )
        )
    return Image.frombytes("RGBA", (width, height), bytes(output))


def encode_rgb565(image: Image.Image) -> bytes:
    source = image.convert("RGB")
    pixels = source.tobytes()
    source.close()
    output = bytearray(image.width * image.height * 2)
    target = 0
    for source_offset in range(0, len(pixels), 3):
        red, green, blue = pixels[source_offset : source_offset + 3]
        value = ((red >> 3) << 11) | ((green >> 2) << 5) | (blue >> 3)
        struct.pack_into("<H", output, target, value)
        target += 2
    return bytes(output)


def encode_rgba4444(image: Image.Image) -> bytes:
    source = image.convert("RGBA")
    pixels = source.tobytes()
    source.close()
    output = bytearray(image.width * image.height * 2)
    target = 0
    for source_offset in range(0, len(pixels), 4):
        red, green, blue, alpha = pixels[source_offset : source_offset + 4]
        value = (
            ((red >> 4) << 12)
            | ((green >> 4) << 8)
            | ((blue >> 4) << 4)
            | (alpha >> 4)
        )
        struct.pack_into("<H", output, target, value)
        target += 2
    return bytes(output)


def sanitized_rgba_bytes(image: Image.Image) -> bytes:
    source = image.convert("RGBA")
    pixels = bytearray(source.tobytes())
    source.close()
    for offset in range(0, len(pixels), 4):
        if pixels[offset + 3] == 0:
            pixels[offset : offset + 3] = b"\0\0\0"
    return bytes(pixels)


def encode_level(image: Image.Image, format_id: int) -> bytes:
    width, height = image.size
    if format_id == FORMAT_RGBA8888_RAW:
        source = image.convert("RGBA")
        encoded = source.tobytes()
        source.close()
    elif format_id == 2:
        encoded = encode_rgb565(image)
    elif format_id == 4:
        encoded = encode_rgba4444(image)
    else:
        padded = None
        source = image
        if width < 4 or height < 4 or width % 4 or height % 4:
            padded = image.resize(
                (max(4, (width + 3) // 4 * 4), max(4, (height + 3) // 4 * 4)),
                Image.Resampling.NEAREST,
            )
            source = padded
        rgba = sanitized_rgba_bytes(source)
        if format_id == 15:
            if etcpak is not None:
                try:
                    encoded = etcpak.compress_etc2_rgb(rgba, source.width, source.height)
                except Exception:
                    if encode_etc2_rgb_pure is None:
                        raise
                    encoded = encode_etc2_rgb_pure(rgba, source.width, source.height)
            elif encode_etc2_rgb_pure is not None:
                encoded = encode_etc2_rgb_pure(rgba, source.width, source.height)
            else:
                raise RuntimeError("ETC2 RGB encoder is unavailable on this build.")
        elif format_id == 16:
            if etcpak is not None:
                try:
                    encoded = etcpak.compress_etc2_rgba(rgba, source.width, source.height)
                except Exception:
                    if encode_etc2_rgba8_pure is None:
                        raise
                    encoded = encode_etc2_rgba8_pure(rgba, source.width, source.height)
            elif encode_etc2_rgba8_pure is not None:
                encoded = encode_etc2_rgba8_pure(rgba, source.width, source.height)
            else:
                raise RuntimeError("ETC2 RGBA8 encoder is unavailable on this build.")
        else:
            raise ValueError(f"unsupported texture format {format_id}")
        if padded is not None:
            padded.close()
    expected = payload_size(format_id, width, height)
    if len(encoded) != expected:
        raise ValueError(
            f"encoder returned {len(encoded)} bytes for {width}x{height} fmt{format_id}; "
            f"expected {expected}"
        )
    return encoded


def encode_texture(image: Image.Image, texture: TextureRecord) -> bytes:
    if not texture.uses_mip_chain:
        return encode_level(image, texture.format_id)
    width, height = texture.width, texture.height
    output = bytearray()
    level = 0
    while True:
        current = (
            image.copy()
            if level == 0
            else image.resize((width, height), Image.Resampling.LANCZOS)
        )
        output.extend(encode_level(current, texture.format_id))
        current.close()
        if width == 1 and height == 1:
            break
        width = max(1, width // 2)
        height = max(1, height // 2)
        level += 1
    if len(output) != texture.encoded_size:
        raise ValueError(
            f"mip chain encoded to {len(output)} bytes; expected {texture.encoded_size}"
        )
    return bytes(output)


def import_png(opened: OpenedIff, texture: TextureRecord, png_path: Path) -> dict[str, object]:
    if texture.payload_offset is None:
        raise ValueError(texture.error or "texture payload location is unknown")
    if not png_path.is_file():
        raise ValueError(f"edited PNG was not found: {png_path}")
    with Image.open(png_path) as source:
        if source.size != (texture.width, texture.height):
            raise ValueError(
                f"edited PNG is {source.width}x{source.height}; expected "
                f"{texture.width}x{texture.height}"
            )
        image = source.convert("RGBA")
    encoded = encode_texture(image, texture)
    image.close()
    if len(encoded) > texture.allocation_size:
        raise ValueError(
            f"encoded texture needs {len(encoded)} bytes but its IFF allocation "
            f"contains only {texture.allocation_size} bytes"
        )
    start = texture.payload_offset
    replacement_offsets = [start]
    if texture.texture_hash in LINKED_RUNTIME_TEXTURE_HASHES:
        original = bytes(opened.data[start : start + len(encoded)])
        if len(original) != len(encoded):
            raise ValueError("linked texture payload is truncated")
        replacement_offsets = []
        search = 0
        while True:
            position = opened.data.find(original, search)
            if position < 0:
                break
            replacement_offsets.append(position)
            search = position + len(original)
        if start not in replacement_offsets:
            raise ValueError("selected linked texture payload was not found in its IFF")
    for replacement_offset in replacement_offsets:
        end = replacement_offset + len(encoded)
        if replacement_offset < 0 or end > len(opened.data):
            raise ValueError("linked texture replacement is outside the IFF")
        opened.data[replacement_offset:end] = encoded
    return {
        "texture": texture.number,
        "png": str(png_path.resolve()),
        "encoded_size": len(encoded),
        "mip_chain": texture.uses_mip_chain,
        "linked_payload_copies_replaced": len(replacement_offsets),
    }


def compress_zlib_max(data: bytes | bytearray) -> bytes:
    """Fast compression for IFF saves, with a high-compression fallback.

    The old implementation ran five full zlib passes for every changed block.
    That is extremely expensive on Android.  Level 6 is normally close enough
    to fit the existing allocation; only if callers need the smallest stream
    do they pay for a level-9 retry.
    """
    return zlib.compress(data, level=6)


def rebuild_compressed_iff(opened: OpenedIff) -> tuple[bytes, str, int]:
    info = opened.wrapper_info
    if info is None:
        return bytes(opened.data), "decompressed", 0
    if len(opened.data) != len(opened.original_data):
        raise ValueError("edited decompressed IFF changed size")

    prepared: list[tuple[WrapperBlock, bytes | None, bool]] = []
    preserve_layout = True
    changed_blocks = 0
    for block in info.blocks:
        start = block.unpacked_offset
        end = start + block.unpacked_size
        modified = bytes(opened.data[start:end])
        original = opened.original_data[start:end]
        changed = modified != original
        packed = compress_zlib_max(modified) if changed else None
        if changed:
            changed_blocks += 1
            if 16 + len(packed) > block.stored_size:
                preserve_layout = False
        prepared.append((block, packed, changed))

    if changed_blocks == 0:
        return opened.source_raw, "unchanged", 0

    if preserve_layout:
        pieces = [opened.source_raw[: info.first_offset]]
        for block, packed, changed in prepared:
            if not changed:
                pieces.append(
                    opened.source_raw[
                        block.position : block.position + block.stored_size
                    ]
                )
                continue
            assert packed is not None
            compact_size = 16 + len(packed)
            pieces.append(
                TYPE_ZLIB
                + struct.pack(
                    ">III",
                    block.unpacked_size,
                    block.declared_stored_size,
                    block.flags,
                )
                + packed
                + b"\0" * (block.stored_size - compact_size)
            )
        last = info.blocks[-1]
        tail = last.position + last.stored_size
        pieces.append(opened.source_raw[tail:])
        rebuilt = b"".join(pieces)
        return rebuilt, "compressed layout preserved", changed_blocks

    compact_blocks: list[bytes] = []
    for block, packed, changed in prepared:
        if not changed:
            compact_blocks.append(
                opened.source_raw[block.position : block.position + block.stored_size]
            )
            continue
        assert packed is not None
        compact_blocks.append(
            TYPE_ZLIB
            + struct.pack(">III", block.unpacked_size, 16 + len(packed), block.flags)
            + packed
        )

    if info.compressed_wrapper:
        prefix = bytearray(opened.source_raw[: info.first_offset])
        position = info.first_offset
        for index, block_bytes in enumerate(compact_blocks):
            descriptor = 0x2C + index * 0x38
            if descriptor + 0x30 > len(prefix):
                raise ValueError("compressed IFF wrapper has no matching block descriptor")
            struct.pack_into("<I", prefix, descriptor + 0x24, position)
            struct.pack_into("<I", prefix, descriptor + 0x2C, len(block_bytes))
            position += len(block_bytes)
        rebuilt_array = bytearray(prefix + b"".join(compact_blocks))
        struct.pack_into(">I", rebuilt_array, 8, len(rebuilt_array))
        rebuilt = bytes(rebuilt_array)
    else:
        rebuilt = b"".join(compact_blocks)
    return rebuilt, "compressed layout compacted", changed_blocks


def save_iff(
    opened: OpenedIff,
    destination: Path,
    *,
    allow_overwrite: bool = False,
) -> dict[str, object]:
    destination = destination.resolve()
    overwriting_source = destination == opened.path
    if overwriting_source and not allow_overwrite:
        raise ValueError(
            "the original IFF is protected; choose a new filename such as *_edited.iff"
        )
    rebuilt, mode, changed_blocks = rebuild_compressed_iff(opened)
    check_data, check_sizes, _wrapper, _info = decompress_wrapper(rebuilt)
    if check_data != bytes(opened.data):
        raise ValueError("saved IFF verification failed: decompressed bytes differ")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix(destination.suffix + ".partial")
    if temporary.exists():
        raise ValueError(f"temporary output already exists: {temporary}")
    try:
        temporary.write_bytes(rebuilt)
        os.replace(temporary, destination)
    finally:
        temporary.unlink(missing_ok=True)
    sidecar = destination.with_suffix(destination.suffix + ".viewer.json")
    sidecar.write_text(
        json.dumps(
            {
                "source_iff": str(opened.path),
                "saved_iff": str(destination),
                "container_mode": mode,
                "changed_compressed_blocks": changed_blocks,
                "decompressed_size": len(opened.data),
                "decompressed_block_sizes": (
                    check_sizes if opened.wrapper_info is not None else opened.block_sizes
                ),
                "verification": "PASS",
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return {
        "output": str(destination),
        "sidecar": str(sidecar),
        "mode": mode,
        "changed_blocks": changed_blocks,
        "size": len(rebuilt),
        "overwrote_source": overwriting_source,
    }


def decode_texture(opened: OpenedIff, texture: TextureRecord) -> Image.Image:
    if texture.payload_offset is None:
        raise ValueError(texture.error or "texture payload location is unknown")
    start = texture.payload_offset
    payload = bytes(opened.data[start : start + texture.payload_size])
    if len(payload) != texture.payload_size:
        raise ValueError("texture payload is truncated")
    if texture.format_id == FORMAT_RGBA8888_RAW:
        return Image.frombytes("RGBA", (texture.width, texture.height), payload)
    if texture.format_id == 2:
        return decode_rgb565(payload, texture.width, texture.height)
    if texture.format_id == 4:
        return decode_rgba4444(payload, texture.width, texture.height)
    if texture.format_id == 15:
        if texture2ddecoder is not None:
            decoded = texture2ddecoder.decode_etc2(payload, texture.width, texture.height)
            texture.decode_layout = "native-linear"
        elif decode_etc2_auto is not None and decode_etc2_pure is not None:
            decoded, layout, score = decode_etc2_auto(
                payload, texture.width, texture.height, rgba8=False,
                preferred_layout=getattr(texture, "decode_layout", "standard"),
            )
            texture.decode_layout = layout
            texture.decode_score = score
        elif decode_etc2_pure is not None:
            decoded = decode_etc2_pure(payload, texture.width, texture.height)
            texture.decode_layout = "standard"
        else:
            raise RuntimeError("ETC2 RGB decoder is unavailable in this build.")
    elif texture.format_id == 16:
        if texture2ddecoder is not None:
            decoded = texture2ddecoder.decode_etc2a8(payload, texture.width, texture.height)
            texture.decode_layout = "native-linear"
        elif decode_etc2_auto is not None and decode_etc2_rgba8_pure is not None:
            decoded, layout, score = decode_etc2_auto(
                payload, texture.width, texture.height, rgba8=True,
                preferred_layout=getattr(texture, "decode_layout", "standard"),
            )
            texture.decode_layout = layout
            texture.decode_score = score
        elif decode_etc2_rgba8_pure is not None:
            decoded = decode_etc2_rgba8_pure(payload, texture.width, texture.height)
            texture.decode_layout = "standard"
        else:
            raise RuntimeError("ETC2 RGBA8 decoder is unavailable in this build.")
    else:
        raise ValueError(f"unsupported texture format {texture.format_id}")
    return Image.frombytes("RGBA", (texture.width, texture.height), decoded, "raw", "BGRA")


def texture_filename(texture: TextureRecord) -> str:
    if texture.label:
        label = re.sub(r"[^A-Za-z0-9._-]+", "_", texture.label).strip("._")
        return (
            f"texture_{texture.number:02d}_{label}_"
            f"{texture.width}x{texture.height}_fmt{texture.format_id}.png"
        )
    return (
        f"texture_{texture.number:02d}_h{texture.texture_hash:08X}_"
        f"{texture.width}x{texture.height}_fmt{texture.format_id}.png"
    )


def export_all(opened: OpenedIff, output_dir: Path) -> tuple[int, list[str]]:
    output_dir.mkdir(parents=True, exist_ok=True)
    exported = 0
    errors: list[str] = []
    records: list[dict[str, object]] = []
    def export_one(texture: TextureRecord) -> tuple[TextureRecord, str | None, str | None]:
        if texture.payload_offset is None:
            return texture, None, texture.error or "payload location is unknown"
        image = None
        try:
            image = decode_texture(opened, texture)
            filename = texture_filename(texture)
            image.save(output_dir / filename)
            return texture, filename, None
        except Exception as error:  # noqa: BLE001
            return texture, None, str(error)
        finally:
            if image is not None:
                image.close()

    # Decoding/PNG encoding is independent per texture.  A small worker pool
    # makes batch export much faster on multicore Android devices without
    # spawning an excessive number of Python threads.
    workers = max(1, min(4, (os.cpu_count() or 2)))
    with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="iff-export") as pool:
        futures = [pool.submit(export_one, texture) for texture in opened.textures]
        results = [future.result() for future in futures]

    for texture, filename, error in results:
        record = texture.as_dict()
        if error is not None:
            errors.append(f"texture #{texture.number}: {error}")
            record["export_error"] = error
        else:
            record["png"] = filename
            exported += 1
        records.append(record)
    manifest = opened.summary()
    manifest["exported_texture_count"] = exported
    manifest["export_errors"] = errors
    manifest["textures"] = records
    (output_dir / "IFF_TEXTURE_MANIFEST.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    return exported, errors


def import_all_exported_pngs(
    opened: OpenedIff, input_dir: Path
) -> dict[str, object]:
    """Import every exactly named PNG produced by :func:`export_all`.

    Matching is case-insensitive for Windows/Photoshop compatibility, but the
    complete exported filename remains authoritative.  A failed encode or
    dimension check restores the original decompressed IFF bytes so a batch can
    never leave only some textures replaced.
    """

    input_dir = input_dir.resolve()
    if not input_dir.is_dir():
        raise ValueError(f"PNG import folder was not found: {input_dir}")
    png_by_name: dict[str, Path] = {}
    duplicates: dict[str, list[Path]] = {}
    for path in input_dir.iterdir():
        if not path.is_file() or path.suffix.lower() != ".png":
            continue
        key = path.name.casefold()
        if key in png_by_name:
            duplicates.setdefault(key, [png_by_name[key]]).append(path)
        else:
            png_by_name[key] = path
    if duplicates:
        names = ", ".join(sorted(paths[0].name for paths in duplicates.values()))
        raise ValueError(f"duplicate case-insensitive PNG filename(s): {names}")

    matched: list[tuple[TextureRecord, Path]] = []
    missing: list[str] = []
    expected_keys: set[str] = set()
    for texture in opened.textures:
        filename = texture_filename(texture)
        key = filename.casefold()
        expected_keys.add(key)
        path = png_by_name.get(key)
        if path is None:
            missing.append(filename)
        else:
            matched.append((texture, path))
    if not matched:
        expected = "\n".join(f"- {texture_filename(texture)}" for texture in opened.textures)
        raise ValueError(
            "the selected folder contains no PNG whose filename matches this IFF's "
            f"exported texture titles. Expected:\n{expected}"
        )

    backup = bytes(opened.data)

    def encode_one(texture: TextureRecord, path: Path):
        if texture.payload_offset is None:
            raise ValueError(texture.error or "payload location is unknown")
        with Image.open(path) as source:
            if source.size != (texture.width, texture.height):
                raise ValueError(
                    f"edited PNG is {source.width}x{source.height}; expected "
                    f"{texture.width}x{texture.height}"
                )
            image = source.convert("RGBA")
        try:
            encoded = encode_texture(image, texture)
        finally:
            image.close()
        if len(encoded) > texture.allocation_size:
            raise ValueError(
                f"encoded texture needs {len(encoded)} bytes but its IFF allocation "
                f"contains only {texture.allocation_size} bytes"
            )
        return texture, encoded, path

    # Encode PNGs concurrently, then patch the shared bytearray on the main
    # thread.  This avoids races while still parallelizing the expensive codec
    # and mipmap work.
    workers = max(1, min(4, (os.cpu_count() or 2)))
    encoded_results = []
    try:
        with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="iff-import") as pool:
            futures = [pool.submit(encode_one, texture, path) for texture, path in matched]
            encoded_results = [future.result() for future in futures]

        changes = []
        for texture, encoded, path in encoded_results:
            start = texture.payload_offset
            assert start is not None
            replacement_offsets = [start]
            if texture.texture_hash in LINKED_RUNTIME_TEXTURE_HASHES:
                original = bytes(opened.data[start : start + len(encoded)])
                replacement_offsets = []
                search = 0
                while True:
                    position = opened.data.find(original, search)
                    if position < 0:
                        break
                    replacement_offsets.append(position)
                    search = position + len(original)
                if start not in replacement_offsets:
                    raise ValueError("selected linked texture payload was not found in its IFF")
            for replacement_offset in replacement_offsets:
                end = replacement_offset + len(encoded)
                if replacement_offset < 0 or end > len(opened.data):
                    raise ValueError("linked texture replacement is outside the IFF")
                opened.data[replacement_offset:end] = encoded
            changes.append({
                "texture": texture.number,
                "png": str(path.resolve()),
                "encoded_size": len(encoded),
                "mip_chain": texture.uses_mip_chain,
                "linked_payload_copies_replaced": len(replacement_offsets),
            })
    except Exception:
        opened.data[:] = backup
        raise
    ignored = sorted(
        path.name for key, path in png_by_name.items() if key not in expected_keys
    )
    return {
        "folder": str(input_dir),
        "matched_count": len(matched),
        "missing_count": len(missing),
        "ignored_png_count": len(ignored),
        "matched": [path.name for _texture, path in matched],
        "missing": missing,
        "ignored": ignored,
        "changes": changes,
        "atomic_rollback_on_error": True,
    }


def resource_filename(resource: ResourceRecord) -> str:
    stem = re.sub(r"[^A-Za-z0-9._-]+", "_", resource.name).strip("._")
    if not stem:
        stem = "resource"
    if resource.extension and stem.lower().endswith(resource.extension.lower()):
        stem = stem[: -len(resource.extension)]
    return (
        f"resource_{resource.number:04d}_off{resource.offset:08X}_"
        f"{stem}{resource.extension}"
    )


def resource_bytes(opened: OpenedIff, resource: ResourceRecord) -> bytes:
    end = resource.offset + resource.size
    if resource.offset < 0 or end > len(opened.data):
        raise ValueError("resource byte range is outside the decompressed IFF")
    return bytes(opened.data[resource.offset:end])


def import_raw_resource(
    opened: OpenedIff, resource: ResourceRecord, replacement: Path
) -> dict[str, object]:
    raw = replacement.read_bytes()
    if len(raw) != resource.size:
        raise ValueError(
            f"raw replacement must be exactly {resource.size:,} bytes; "
            f"selected file is {len(raw):,} bytes"
        )
    start = resource.offset
    end = start + resource.size
    opened.data[start:end] = raw
    return {
        "resource_number": resource.number,
        "resource_name": resource.name,
        "offset": f"0x{start:X}",
        "size": resource.size,
        "replacement": str(replacement.resolve()),
        "mode": "exact-size raw replacement",
    }


def export_all_resources(opened: OpenedIff, output_dir: Path) -> tuple[int, int]:
    """Export non-container rows; together they cover every decompressed byte."""

    output_dir.mkdir(parents=True, exist_ok=True)
    exported = 0
    exported_bytes = 0
    records: list[dict[str, object]] = []
    for resource in opened.resources:
        record = resource.as_dict()
        if resource.container:
            record["exported"] = False
            record["note"] = "overview row; child resources provide byte-exact coverage"
        else:
            filename = resource_filename(resource)
            (output_dir / filename).write_bytes(resource_bytes(opened, resource))
            record["exported"] = True
            record["file"] = filename
            exported += 1
            exported_bytes += resource.size
        records.append(record)
    coverage = "PASS" if exported_bytes == len(opened.data) else "CHECK"
    manifest = {
        "source_iff": str(opened.path),
        "wrapper": opened.wrapper,
        "decompressed_size": len(opened.data),
        "block_sizes": opened.block_sizes,
        "resource_count": len(opened.resources),
        "exported_leaf_count": exported,
        "exported_leaf_bytes": exported_bytes,
        "byte_coverage_verification": coverage,
        "important_note": (
            "NBA 2K IFF objects do not all store normal filenames. Rows named "
            "Unclassified region are byte-exact exports, not invented file types."
        ),
        "resources": records,
    }
    (output_dir / "IFF_ALL_RESOURCES_MANIFEST.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    return exported, exported_bytes


def resource_preview_text(opened: OpenedIff, resource: ResourceRecord) -> str:
    heading = (
        f"{resource.name}\n"
        f"Kind: {resource.kind}   Offset: 0x{resource.offset:X}   "
        f"Size: {resource.size:,} bytes\n"
        f"Detection: {resource.confidence}   {resource.details}\n\n"
    )
    if resource.extension in (".glsl", ".xml", ".txt"):
        preview_size = min(resource.size, 16000)
        raw = bytes(opened.data[resource.offset : resource.offset + preview_size])
        text = raw.decode("utf-8", errors="replace")
        if resource.size > preview_size:
            text += "\n\n[preview truncated]"
        return heading + text

    preview_size = min(resource.size, RESOURCE_PREVIEW_BYTES)
    preview = bytes(opened.data[resource.offset : resource.offset + preview_size])
    lines: list[str] = []
    for local in range(0, len(preview), 16):
        chunk = preview[local : local + 16]
        hexadecimal = " ".join(f"{value:02X}" for value in chunk)
        ascii_text = "".join(chr(value) if 32 <= value <= 126 else "." for value in chunk)
        lines.append(
            f"{resource.offset + local:08X}  {hexadecimal:<47}  {ascii_text}"
        )
    if resource.size > len(preview):
        lines.append(
            f"\n[hex preview truncated; {resource.size - len(preview):,} more bytes]"
        )
    return heading + "\n".join(lines)


def catalog_path_for(folder: Path) -> Path:
    return folder.resolve() / CATALOG_FILENAME


def _open_catalog(path: Path) -> sqlite3.Connection:
    connection = sqlite3.connect(path)
    connection.execute("PRAGMA journal_mode=WAL")
    connection.execute("PRAGMA synchronous=NORMAL")
    connection.executescript(
        """
        CREATE TABLE IF NOT EXISTS files (
            relative_path TEXT PRIMARY KEY,
            source_size INTEGER NOT NULL,
            modified_ns INTEGER NOT NULL,
            wrapper TEXT,
            decoded_size INTEGER,
            block_sizes TEXT,
            texture_count INTEGER DEFAULT 0,
            previewable_textures INTEGER DEFAULT 0,
            resource_count INTEGER DEFAULT 0,
            known_resource_count INTEGER DEFAULT 0,
            unknown_resource_count INTEGER DEFAULT 0,
            byte_coverage INTEGER DEFAULT 0,
            status TEXT NOT NULL,
            error TEXT,
            scanned_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS resources (
            relative_path TEXT NOT NULL,
            resource_number INTEGER NOT NULL,
            kind TEXT NOT NULL,
            name TEXT NOT NULL,
            offset INTEGER NOT NULL,
            size INTEGER NOT NULL,
            extension TEXT,
            details TEXT,
            confidence TEXT,
            texture_number INTEGER,
            PRIMARY KEY (relative_path, resource_number)
        );
        CREATE INDEX IF NOT EXISTS resources_kind_index ON resources(kind);
        CREATE INDEX IF NOT EXISTS resources_name_index ON resources(name);
        CREATE TABLE IF NOT EXISTS metadata (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );
        """
    )
    stored = connection.execute(
        "SELECT value FROM metadata WHERE key = 'parser_version'"
    ).fetchone()
    if stored is None:
        connection.execute(
            "INSERT INTO metadata(key, value) VALUES('parser_version', ?)",
            (CATALOG_PARSER_VERSION,),
        )
        connection.commit()
    elif stored[0] != CATALOG_PARSER_VERSION:
        # A future parser revision may change offsets/types.  Invalidate only
        # the index, never an IFF, then let the normal resumable scan rebuild it.
        connection.execute("DELETE FROM resources")
        connection.execute("DELETE FROM files")
        connection.execute(
            "UPDATE metadata SET value = ? WHERE key = 'parser_version'",
            (CATALOG_PARSER_VERSION,),
        )
        connection.commit()
    return connection


def build_folder_catalog(
    folder: Path,
    *,
    database: Path | None = None,
    progress=None,
    cancel_event: threading.Event | None = None,
) -> dict[str, object]:
    """Build or resume a persistent searchable index for every IFF in a folder."""

    folder = folder.resolve()
    files = find_iff_files(folder)
    database = (database or catalog_path_for(folder)).resolve()
    database.parent.mkdir(parents=True, exist_ok=True)
    connection = _open_catalog(database)
    scanned = 0
    cached = 0
    errors = 0
    started = time.monotonic()
    try:
        existing = {
            row[0]: (row[1], row[2], row[3])
            for row in connection.execute(
                "SELECT relative_path, source_size, modified_ns, status FROM files"
            )
        }
        for index, path in enumerate(files, 1):
            if cancel_event is not None and cancel_event.is_set():
                break
            relative = str(path.relative_to(folder)).replace("\\", "/")
            stat = path.stat()
            old = existing.get(relative)
            if old == (stat.st_size, stat.st_mtime_ns, "OK"):
                cached += 1
                if progress is not None:
                    progress(index, len(files), path, "cached", None)
                continue
            try:
                opened = open_iff(path)
                leaf = [resource for resource in opened.resources if not resource.container]
                known = [
                    resource
                    for resource in leaf
                    if resource.kind != "Unclassified binary"
                ]
                unknown = [
                    resource
                    for resource in leaf
                    if resource.kind == "Unclassified binary"
                ]
                coverage = sum(resource.size for resource in leaf)
                previewable = sum(
                    texture.payload_offset is not None for texture in opened.textures
                )
                connection.execute(
                    "DELETE FROM resources WHERE relative_path = ?", (relative,)
                )
                connection.executemany(
                    """
                    INSERT INTO resources (
                        relative_path, resource_number, kind, name, offset, size,
                        extension, details, confidence, texture_number
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    [
                        (
                            relative,
                            resource.number,
                            resource.kind,
                            resource.name,
                            resource.offset,
                            resource.size,
                            resource.extension,
                            resource.details,
                            resource.confidence,
                            resource.texture_number,
                        )
                        for resource in leaf
                    ],
                )
                connection.execute(
                    """
                    INSERT OR REPLACE INTO files (
                        relative_path, source_size, modified_ns, wrapper,
                        decoded_size, block_sizes, texture_count,
                        previewable_textures, resource_count,
                        known_resource_count, unknown_resource_count,
                        byte_coverage, status, error, scanned_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'OK', NULL, ?)
                    """,
                    (
                        relative,
                        stat.st_size,
                        stat.st_mtime_ns,
                        opened.wrapper,
                        len(opened.data),
                        json.dumps(opened.block_sizes),
                        len(opened.textures),
                        previewable,
                        len(leaf),
                        len(known),
                        len(unknown),
                        coverage,
                        time.strftime("%Y-%m-%d %H:%M:%S"),
                    ),
                )
                scanned += 1
                outcome = "scanned"
                error_text = None
            except Exception as error:  # noqa: BLE001 - retain per-file diagnostics
                connection.execute(
                    "DELETE FROM resources WHERE relative_path = ?", (relative,)
                )
                connection.execute(
                    """
                    INSERT OR REPLACE INTO files (
                        relative_path, source_size, modified_ns, status, error, scanned_at
                    ) VALUES (?, ?, ?, 'ERROR', ?, ?)
                    """,
                    (
                        relative,
                        stat.st_size,
                        stat.st_mtime_ns,
                        str(error),
                        time.strftime("%Y-%m-%d %H:%M:%S"),
                    ),
                )
                errors += 1
                outcome = "error"
                error_text = str(error)
            if index % 10 == 0:
                connection.commit()
            if progress is not None:
                progress(index, len(files), path, outcome, error_text)
        connection.commit()
    finally:
        connection.close()
    cancelled = cancel_event is not None and cancel_event.is_set()
    return {
        "folder": str(folder),
        "database": str(database),
        "file_count": len(files),
        "scanned": scanned,
        "cached": cached,
        "errors": errors,
        "cancelled": cancelled,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }


def catalog_file_results(folder: Path) -> dict[Path, str]:
    database = catalog_path_for(folder)
    if not database.is_file():
        return {}
    connection = sqlite3.connect(database)
    try:
        rows = connection.execute(
            """
            SELECT relative_path, previewable_textures, texture_count,
                   known_resource_count, unknown_resource_count, status
            FROM files
            """
        ).fetchall()
    finally:
        connection.close()
    results: dict[Path, str] = {}
    for relative, previewable, textures, known, unknown, status in rows:
        path = (folder / relative).resolve()
        if status == "OK":
            results[path] = f"{previewable}/{textures} T | {known}+{unknown} R"
        else:
            results[path] = "ERROR"
    return results


def catalog_matching_files(folder: Path, query_text: str) -> set[Path]:
    database = catalog_path_for(folder)
    if not database.is_file() or not query_text.strip():
        return set()
    pattern = f"%{query_text.strip()}%"
    connection = sqlite3.connect(database)
    try:
        rows = connection.execute(
            """
            SELECT DISTINCT relative_path FROM resources
            WHERE kind LIKE ? COLLATE NOCASE
               OR name LIKE ? COLLATE NOCASE
               OR details LIKE ? COLLATE NOCASE
               OR extension LIKE ? COLLATE NOCASE
            """,
            (pattern, pattern, pattern, pattern),
        ).fetchall()
    finally:
        connection.close()
    return {(folder / row[0]).resolve() for row in rows}


def catalog_resource_kinds(folder: Path) -> list[str]:
    """Return the detected resource kinds currently present in the catalog."""

    database = catalog_path_for(folder)
    if not database.is_file():
        return []
    connection = sqlite3.connect(database, timeout=10)
    try:
        return [
            row[0]
            for row in connection.execute(
                "SELECT DISTINCT kind FROM resources ORDER BY kind COLLATE NOCASE"
            )
        ]
    finally:
        connection.close()


def catalog_resource_rows(
    folder: Path,
    *,
    query_text: str = "",
    kind: str = "",
    limit: int = 2500,
) -> tuple[list[tuple], int]:
    """Read a bounded, searchable folder-wide resource view from SQLite.

    The table may contain hundreds of thousands of rows, so the GUI displays a
    bounded page while reporting the complete match count.  Searching and kind
    filtering happen in SQLite rather than requiring each IFF to be reopened.
    """

    database = catalog_path_for(folder)
    if not database.is_file():
        return [], 0
    conditions: list[str] = []
    parameters: list[object] = []
    query_text = query_text.strip()
    kind = kind.strip()
    if query_text:
        pattern = f"%{query_text}%"
        conditions.append(
            "(relative_path LIKE ? COLLATE NOCASE "
            "OR kind LIKE ? COLLATE NOCASE "
            "OR name LIKE ? COLLATE NOCASE "
            "OR details LIKE ? COLLATE NOCASE "
            "OR extension LIKE ? COLLATE NOCASE)"
        )
        parameters.extend([pattern] * 5)
    if kind and kind != "All kinds":
        conditions.append("kind = ? COLLATE NOCASE")
        parameters.append(kind)
    where = " WHERE " + " AND ".join(conditions) if conditions else ""
    connection = sqlite3.connect(database, timeout=10)
    try:
        total = connection.execute(
            "SELECT COUNT(*) FROM resources" + where, parameters
        ).fetchone()[0]
        rows = connection.execute(
            """
            SELECT relative_path, resource_number, kind, name, offset, size,
                   extension, details, confidence, texture_number
            FROM resources
            """
            + where
            + " ORDER BY relative_path COLLATE NOCASE, resource_number LIMIT ?",
            [*parameters, max(1, int(limit))],
        ).fetchall()
    finally:
        connection.close()
    return rows, total


def checker_preview(image: Image.Image, maximum: tuple[int, int]) -> Image.Image:
    preview = image.convert("RGBA")
    preview.thumbnail(maximum, Image.Resampling.LANCZOS)
    checker = Image.new("RGB", preview.size, "#5A5A5A")
    draw = ImageDraw.Draw(checker)
    cell = 16
    for y in range(0, checker.height, cell):
        for x in range(0, checker.width, cell):
            if (x // cell + y // cell) % 2:
                draw.rectangle((x, y, x + cell - 1, y + cell - 1), fill="#777777")
    checker.paste(preview, (0, 0), preview)
    preview.close()
    return checker


TEXTURE_PREVIEW_MODES = (
    "RGB (ignore alpha)",
    "RGBA + checker",
    "Alpha channel",
    "Red channel",
    "Green channel",
    "Blue channel",
)


def texture_editing_preview(
    image: Image.Image,
    maximum: tuple[int, int],
    mode: str = "RGB (ignore alpha)",
    pixel_sharp: bool = True,
) -> Image.Image:
    """Build a clear editing preview without changing export/import pixels."""

    rgba = image.convert("RGBA")
    if mode == "RGBA + checker":
        visible = rgba
    elif mode == "Alpha channel":
        alpha = rgba.getchannel("A")
        visible = Image.merge("RGBA", (alpha, alpha, alpha, Image.new("L", alpha.size, 255)))
        alpha.close()
        rgba.close()
    elif mode in ("Red channel", "Green channel", "Blue channel"):
        channel_name = mode[0]
        channel = rgba.getchannel(channel_name)
        visible = Image.merge(
            "RGBA", (channel, channel, channel, Image.new("L", channel.size, 255))
        )
        channel.close()
        rgba.close()
    else:
        visible = rgba.convert("RGB").convert("RGBA")
        rgba.close()

    width, height = visible.size
    fit_scale = min(maximum[0] / width, maximum[1] / height)
    if pixel_sharp and fit_scale >= 1:
        scale = max(1, int(fit_scale))
        target = (width * scale, height * scale)
    else:
        scale = min(1.0, fit_scale) if pixel_sharp else fit_scale
        target = (
            max(1, int(round(width * scale))),
            max(1, int(round(height * scale))),
        )
    resampling = Image.Resampling.NEAREST if pixel_sharp else Image.Resampling.LANCZOS
    preview = visible if target == visible.size else visible.resize(target, resampling)
    if preview is not visible:
        visible.close()

    if mode != "RGBA + checker":
        output = preview.convert("RGB")
        preview.close()
        return output

    cell = max(8, min(24, max(1, target[0] // max(1, width)) * 8))
    output = Image.new("RGB", target, "#D8D8D8")
    draw = ImageDraw.Draw(output)
    for y in range(0, target[1], cell):
        for x in range(0, target[0], cell):
            if (x // cell + y // cell) % 2:
                draw.rectangle((x, y, x + cell - 1, y + cell - 1), fill="#A8A8A8")
    output.paste(preview, (0, 0), preview)
    preview.close()
    return output


class Viewer:
    @staticmethod
    def _android_download_dir() -> Path:
        """Return a normal shared-storage folder writable by Pydroid on Android."""
        candidates = (
            Path("/storage/emulated/0/Download"),
            Path("/sdcard/Download"),
            Path.home() / "Download",
        )
        for folder in candidates:
            try:
                folder.mkdir(parents=True, exist_ok=True)
                probe = folder / ".nba2k20_write_test"
                probe.write_bytes(b"ok")
                probe.unlink(missing_ok=True)
                return folder
            except Exception:
                continue
        raise OSError(
            "Pydroid cannot write to shared storage. Grant Pydroid 3 storage/files "
            "permission, then try again."
        )

    @staticmethod
    def _destination_is_writable(destination: Path) -> None:
        """Fail early before a large OBB rebuild if Android blocks the destination."""
        destination = destination.resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        probe = destination.parent / ("." + destination.name + ".write_test")
        try:
            probe.write_bytes(b"ok")
        finally:
            probe.unlink(missing_ok=True)

    def __init__(self, initial: Path | None):
        import tkinter as tk
        from tkinter import filedialog, messagebox, ttk

        self.tk = tk
        self.ttk = ttk
        self.filedialog = filedialog
        self.messagebox = messagebox
        self.root = tk.Tk()

        # Android/Pydroid 3 uses the device display scaling for Tk by default.
        # On many phones that makes ttk controls and headings several times
        # larger than the available width.  Keep the desktop UI intact, but
        # switch to a compact, touch-friendly theme on narrow/high-DPI screens.
        self.root.update_idletasks()
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        self.mobile_ui = screen_w <= 900 or (screen_h > screen_w * 1.35)

        if self.mobile_ui:
            # Samsung A52/A52s class phones: use a comfortable physical text
            # size instead of Tk's 1.0 scaling, which makes 9-10pt text look
            # microscopic on Pydroid.  1.25 is a good middle ground for the
            # 1080x2400 portrait display while still leaving room for controls.
            try:
                self.root.tk.call("tk", "scaling", 1.50)
            except Exception:
                pass
            self.root.geometry(f"{screen_w}x{max(700, screen_h - 55)}")
            self.root.minsize(360, 650)
        else:
            self.root.geometry("1180x760")
            self.root.minsize(900, 600)

        # Explicit, readable Android sizes.  The old mobile build used 9-10pt
        # everywhere, which is too small on a high-density Samsung display.
        import tkinter.font as tkfont
        font_size = 15 if self.mobile_ui else 10
        small_font_size = 13 if self.mobile_ui else 9
        heading_font_size = 14 if self.mobile_ui else 10
        for font_name, size in (
            ("TkDefaultFont", font_size),
            ("TkTextFont", font_size),
            ("TkMenuFont", font_size),
            ("TkHeadingFont", heading_font_size),
            ("TkCaptionFont", font_size + 1 if self.mobile_ui else 11),
            ("TkSmallCaptionFont", small_font_size),
        ):
            try:
                tkfont.nametofont(font_name).configure(size=size)
            except Exception:
                pass

        self.root.title("NBA 2K20 • IFF / OBB Manager")

        style = ttk.Style(self.root)
        try:
            if "clam" in style.theme_names():
                style.theme_use("clam")
        except Exception:
            pass

        accent = "#F5C928"
        navy = "#101A35"
        panel = "#E7E7E7"
        text_dark = "#111111"
        style.configure("TFrame", background=navy)
        style.configure("TLabel", background=navy, foreground="#F2F2F2",
                        font=("TkDefaultFont", font_size))
        style.configure("TButton", font=("TkDefaultFont", font_size),
                        padding=((8, 6) if self.mobile_ui else (8, 6)),
                        background=accent, foreground=text_dark)
        style.configure("TCheckbutton", font=("TkDefaultFont", font_size),
                        background=navy, foreground="#F2F2F2")
        style.configure("TNotebook", background=navy)
        style.configure("TNotebook.Tab", font=("TkDefaultFont", font_size),
                        padding=((12, 7) if self.mobile_ui else (10, 6)),
                        background=panel, foreground=text_dark)
        style.configure("Treeview", font=("TkDefaultFont", small_font_size),
                        rowheight=(32 if self.mobile_ui else 26), background="white",
                        fieldbackground="white", foreground=text_dark)
        style.configure("Treeview.Heading", font=("TkDefaultFont", small_font_size),
                        padding=((8, 8) if self.mobile_ui else (5, 5)))
        style.configure("TEntry", font=("TkDefaultFont", font_size), padding=(8 if self.mobile_ui else 5))
        style.configure("TCombobox", font=("TkDefaultFont", font_size),
                        padding=(7 if self.mobile_ui else 3))
        style.configure("Horizontal.TProgressbar", thickness=8)
        style.map("TButton",
                  background=[("disabled", "#BDBDBD"), ("active", "#FFD84A"),
                              ("pressed", "#D9AE12")],
                  foreground=[("disabled", "#777777"), ("active", text_dark),
                              ("pressed", text_dark)])
        style.map("TNotebook.Tab",
                  background=[("selected", accent), ("active", "#FFD84A")],
                  foreground=[("selected", text_dark)])
        self._ui_navy = navy
        self._ui_accent = accent
        self._ui_panel = panel
        try:
            self.root.configure(bg=navy)
        except Exception:
            pass
        self.opened: OpenedIff | None = None
        self.preview_photo = None
        self.texture_preview_mode_var = tk.StringVar(value="RGB (ignore alpha)")
        self.texture_preview_sharp_var = tk.BooleanVar(value=True)
        self.dirty = False
        self.changes: list[dict[str, object]] = []
        self.folder_root: Path | None = None
        self.folder_files: list[Path] = []
        self.visible_files: list[Path] = []
        self.file_source_mode = "folder"
        self.file_results: dict[Path, str] = {}
        self.suppress_file_event = False
        self.file_sort_column: str | None = None
        self.file_sort_descending = False
        self.filter_after_id = None
        self.catalog_filter_after_id = None
        self.catalog_rows: list[tuple] = []
        self.catalog_queue: queue.Queue = queue.Queue()
        self.catalog_thread: threading.Thread | None = None
        self.catalog_cancel = threading.Event()
        self.external_temp = tempfile.TemporaryDirectory(prefix="nba2k20_iff_open_")
        self.obb_session: DirectObbSession | None = None
        self.obb_current_index: int | None = None
        self.obb_rows: list[tuple] = []
        self.visible_obb_rows: list[tuple] = []
        self.obb_iff_rows: list[tuple] = []
        self.visible_obb_iff_rows: list[tuple] = []
        self.obb_entry_results: dict[int, str] = {}
        self.obb_browser = None
        self.obb_save_queue: queue.Queue = queue.Queue()
        self.obb_save_thread: threading.Thread | None = None
        self.open_queue: queue.Queue = queue.Queue()
        self.open_thread: threading.Thread | None = None
        self.open_generation = 0

        toolbar = ttk.Frame(self.root, padding=(8, 6))
        toolbar.pack(fill="x")

        if self.mobile_ui:
            # Two-column touch layout: readable labels without squeezing four
            # tiny buttons into one row.
            for col in range(2):
                toolbar.columnconfigure(col, weight=1, uniform="mobile_btn")
            mobile_buttons = [
                ("Open IFF", self.choose_file),
                ("Open Folder", self.choose_folder),
                ("Previous IFF", lambda: self.move_file(-1)),
                ("Next IFF", lambda: self.move_file(1)),
                ("Import Edited PNG", self.import_selected),
                ("Import All PNGs", self.import_all_exported),
                ("Save IFF", self.save_current),
                ("Save IFF Copy", self.save_copy),
                ("Export Selected PNG", self.export_selected),
                ("Export Selected JPEG", self.export_selected_jpeg),
                ("Export All PNG", self.export_everything),
                ("Auto Fix ETC2", self.auto_fix_selected_etc2),
            ]
            for i, (label, command) in enumerate(mobile_buttons):
                ttk.Button(toolbar, text=label, command=command).grid(
                    row=i // 2, column=i % 2, sticky="ew", padx=3, pady=3
                )
        else:
            ttk.Button(toolbar, text="Open IFF", command=self.choose_file).pack(side="left")
            ttk.Button(toolbar, text="Open Folder", command=self.choose_folder).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Previous IFF", command=lambda: self.move_file(-1)).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Next IFF", command=lambda: self.move_file(1)).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Import Edited PNG", command=self.import_selected).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Import All PNGs", command=self.import_all_exported).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Save IFF", command=self.save_current).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Save IFF Copy", command=self.save_copy).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Export Selected PNG", command=self.export_selected).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Export Selected JPEG", command=self.export_selected_jpeg).pack(
                side="left", padx=(8, 0)
            )
            ttk.Button(toolbar, text="Export All PNG", command=self.export_everything).pack(
                side="left", padx=(8, 0)
            )

        self.file_label = ttk.Label(toolbar, text="No IFF opened")
        if self.mobile_ui:
            self.file_label.grid(row=(len(mobile_buttons) + 1) // 2, column=0, columnspan=2, sticky="w", padx=4, pady=(2, 0))
        else:
            self.file_label.pack(side="left", padx=16)

        obb_toolbar = ttk.Frame(self.root, padding=(8, 0, 8, 8))
        obb_toolbar.pack(fill="x")
        if self.mobile_ui:
            for col in range(2):
                obb_toolbar.columnconfigure(col, weight=1, uniform="obb_btn")
        ttk.Button(obb_toolbar, text="Open OBB", command=self.choose_obb).grid(
            row=0, column=0, sticky="ew", padx=3, pady=2
        ) if self.mobile_ui else ttk.Button(obb_toolbar, text="Open OBB", command=self.choose_obb).pack(side="left")
        self.obb_browse_button = ttk.Button(
            obb_toolbar,
            text="OBB Entries",
            command=self.show_obb_browser,
            state="disabled",
        )
        if self.mobile_ui:
            self.obb_browse_button.grid(row=0, column=1, sticky="ew", padx=3, pady=2)
        else:
            self.obb_browse_button.pack(side="left", padx=(8, 0))
        self.obb_export_iff_button = ttk.Button(
            obb_toolbar,
            text="Export IFF",
            command=self.export_current_obb_iff,
            state="disabled",
        )
        if self.mobile_ui:
            self.obb_export_iff_button.grid(row=1, column=0, sticky="ew", padx=3, pady=2)
        else:
            self.obb_export_iff_button.pack(side="left", padx=(8, 0))
        self.obb_import_iff_button = ttk.Button(
            obb_toolbar,
            text="Import / Replace IFF",
            command=self.import_replace_current_obb_iff,
            state="disabled",
        )
        if self.mobile_ui:
            self.obb_import_iff_button.grid(row=1, column=1, sticky="ew", padx=3, pady=2)
        else:
            self.obb_import_iff_button.pack(side="left", padx=(8, 0))
        self.obb_save_button = ttk.Button(
            obb_toolbar,
            text="Save OBB",
            command=self.save_current_obb,
            state="disabled",
        )
        if self.mobile_ui:
            self.obb_save_button.grid(row=2, column=0, sticky="ew", padx=3, pady=2)
        else:
            self.obb_save_button.pack(side="left", padx=(8, 0))
        self.obb_save_copy_button = ttk.Button(
            obb_toolbar,
            text="Save OBB Copy",
            command=self.save_obb_copy,
            state="disabled",
        )
        if self.mobile_ui:
            self.obb_save_copy_button.grid(row=2, column=1, sticky="ew", padx=3, pady=2)
        else:
            self.obb_save_copy_button.pack(side="left", padx=(8, 0))
        self.obb_progress = ttk.Progressbar(
            obb_toolbar, mode="indeterminate", length=130
        )
        if self.mobile_ui:
            self.obb_progress.grid(row=3, column=0, sticky="ew", padx=3, pady=2)
        else:
            self.obb_progress.pack(side="left", padx=(10, 0))
        self.obb_label_var = tk.StringVar(value="No OBB opened")
        if self.mobile_ui:
            ttk.Label(obb_toolbar, textvariable=self.obb_label_var).grid(
                row=3, column=1, sticky="w", padx=5, pady=2
            )
        else:
            ttk.Label(obb_toolbar, textvariable=self.obb_label_var).pack(
                side="left", padx=(10, 0)
            )

        pane = ttk.Panedwindow(
            self.root, orient="vertical" if self.mobile_ui else "horizontal"
        )
        pane.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        left = ttk.Panedwindow(pane, orient="vertical")
        right = ttk.Frame(pane)
        if self.mobile_ui:
            # Android Tkinter/Pydroid can ignore Panedwindow weights when the
            # lower pane has many widgets, leaving the preview only a tiny strip.
            # Keep the vertical Panedwindow, but explicitly position its sash
            # after layout so the preview gets a real, usable height.
            pane.add(right, weight=1)
            pane.add(left, weight=1)
            self._mobile_preview_pane = pane
        else:
            pane.add(left, weight=2)
            pane.add(right, weight=3)

        file_frame = ttk.Frame(left)
        texture_frame = ttk.Frame(left)
        left.add(file_frame, weight=2)
        left.add(texture_frame, weight=3)

        file_controls = ttk.Frame(file_frame, padding=(0, 0, 0, 5))
        file_controls.pack(fill="x")
        self.folder_label_var = tk.StringVar(value="IFF files: open a folder")
        if self.mobile_ui:
            file_controls.columnconfigure(1, weight=1)
            ttk.Label(file_controls, textvariable=self.folder_label_var).grid(
                row=0, column=0, columnspan=2, sticky="w", padx=3, pady=(0, 3)
            )
        else:
            ttk.Label(file_controls, textvariable=self.folder_label_var).pack(
                side="left", padx=(2, 8)
            )
        self.catalog_button = ttk.Button(
            file_controls, text="Build / Update Catalog", command=self.start_catalog
        )
        self.catalog_cancel_button = ttk.Button(
            file_controls, text="Cancel", command=self.cancel_catalog, state="disabled"
        )
        self.filter_var = tk.StringVar()
        filter_entry = ttk.Entry(file_controls, textvariable=self.filter_var, width=24)
        self.filter_entry = filter_entry
        if self.mobile_ui:
            self.catalog_button.grid(row=1, column=0, sticky="ew", padx=3, pady=2)
            self.catalog_cancel_button.grid(row=1, column=1, sticky="ew", padx=3, pady=2)
            ttk.Label(file_controls, text="Search:").grid(row=2, column=0, sticky="w", padx=3)
            filter_entry.grid(row=2, column=1, sticky="ew", padx=3, pady=2)
        else:
            self.catalog_button.pack(side="left", padx=(0, 6))
            self.catalog_cancel_button.pack(side="left", padx=(0, 8))
            ttk.Label(file_controls, text="Search:").pack(side="left")
            filter_entry.pack(side="left", fill="x", expand=True, padx=(4, 2))

        file_columns = ("name", "size", "folder", "result")
        self.file_tree = ttk.Treeview(
            file_frame,
            columns=file_columns,
            show="headings",
            selectmode="browse",
            height=12,
        )
        file_headings = {
            "name": "IFF file",
            "size": "Size",
            "folder": "Relative folder",
            "result": "Contents",
        }
        file_widths = {"name": 220, "size": 70, "folder": 170, "result": 80}
        for column in file_columns:
            self.file_tree.heading(
                column,
                text=file_headings[column],
                command=lambda selected=column: self.sort_file_list(selected),
            )
            self.file_tree.column(column, width=file_widths[column], anchor="w")
        file_scrollbar = ttk.Scrollbar(
            file_frame, orient="vertical", command=self.file_tree.yview
        )
        self.file_tree.configure(yscrollcommand=file_scrollbar.set)
        self.file_tree.pack(side="left", fill="both", expand=True)
        file_scrollbar.pack(side="right", fill="y")
        self.file_tree.bind("<<TreeviewSelect>>", self.on_file_select)
        self.filter_var.trace_add("write", lambda *_arguments: self.schedule_file_refresh())

        self.detail_notebook = ttk.Notebook(texture_frame)
        self.detail_notebook.pack(fill="both", expand=True)
        self.texture_tab = ttk.Frame(self.detail_notebook)
        self.model_tab = ttk.Frame(self.detail_notebook)
        self.resource_tab = ttk.Frame(self.detail_notebook)
        self.catalog_tab = ttk.Frame(self.detail_notebook)
        self.detail_notebook.add(self.texture_tab, text="Textures")
        self.detail_notebook.add(self.model_tab, text="3D Models")
        self.detail_notebook.add(self.resource_tab, text="Current IFF Resources")
        self.detail_notebook.add(self.catalog_tab, text="All IFF Contents")
        self.detail_notebook.bind("<<NotebookTabChanged>>", self._on_detail_tab_changed)

        texture_controls = ttk.Frame(self.texture_tab, padding=(3, 3, 3, 5))
        texture_controls.pack(fill="x")
        ttk.Button(
            texture_controls,
            text="Show RGBA8888 Atlas",
            command=self.show_uniform_visual,
        ).pack(side="left")
        ttk.Label(texture_controls, text="View:").pack(side="left", padx=(12, 3))
        texture_mode = ttk.Combobox(
            texture_controls,
            textvariable=self.texture_preview_mode_var,
            values=TEXTURE_PREVIEW_MODES,
            state="readonly",
            width=18,
        )
        texture_mode.pack(side="left")
        texture_mode.bind("<<ComboboxSelected>>", self.on_select)
        ttk.Checkbutton(
            texture_controls,
            text="Pixel-sharp",
            variable=self.texture_preview_sharp_var,
            command=self.on_select,
        ).pack(side="left", padx=(8, 0))
        ttk.Label(
            texture_controls,
            text="Export/import stays at the original texture size",
        ).pack(side="left", padx=(8, 0))

        columns = ("number", "filename", "size", "format", "location", "hash")
        texture_list_frame = ttk.Frame(self.texture_tab)
        texture_list_frame.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(
            texture_list_frame,
            columns=columns,
            show="headings",
            selectmode="browse",
        )
        headings = {
            "number": "#",
            "filename": "Export filename",
            "size": "Dimensions",
            "format": "Format",
            "location": "Payload",
            "hash": "Texture hash",
        }
        if self.mobile_ui:
            # Keep every texture column on-screen on narrow Android displays.
            # The previous desktop widths forced a horizontal scroll, making
            # filename/dimensions/format appear missing on phones.
            widths = {
                "number": 34,
                "filename": 180,
                "size": 76,
                "format": 78,
                "location": 150,
                "hash": 82,
            }
        else:
            widths = {
                "number": 42,
                "filename": 390,
                "size": 100,
                "format": 105,
                "location": 250,
                "hash": 105,
            }
        for column in columns:
            self.tree.heading(column, text=headings[column])
            self.tree.column(column, width=widths[column], anchor="w")
        texture_list_frame.rowconfigure(0, weight=1)
        texture_list_frame.columnconfigure(0, weight=1)
        scrollbar = ttk.Scrollbar(
            texture_list_frame, orient="vertical", command=self.tree.yview
        )
        horizontal_scrollbar = ttk.Scrollbar(
            texture_list_frame, orient="horizontal", command=self.tree.xview
        )
        self.tree.configure(
            yscrollcommand=scrollbar.set,
            xscrollcommand=horizontal_scrollbar.set,
        )
        self.tree.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")
        horizontal_scrollbar.grid(row=1, column=0, sticky="ew")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)

        model_controls = ttk.Frame(self.model_tab, padding=(3, 3, 3, 5))
        model_controls.pack(fill="x")
        ttk.Button(
            model_controls,
            text="Export Selected OBJ",
            command=self.export_selected_model,
        ).pack(side="left")
        ttk.Button(
            model_controls,
            text="Import Edited OBJ",
            command=self.import_selected_model,
        ).pack(side="left", padx=(6, 0))
        ttk.Button(
            model_controls,
            text="Export All OBJ",
            command=self.export_every_model,
        ).pack(side="left", padx=(6, 0))
        ttk.Label(
            model_controls,
            text="Only validated layouts appear; packed/shared streams remain under Resources",
        ).pack(side="left", padx=(10, 0))
        model_list_frame = ttk.Frame(self.model_tab)
        model_list_frame.pack(fill="both", expand=True)
        model_columns = (
            "number", "vertices", "triangles", "stride", "topology", "details"
        )
        self.model_tree = ttk.Treeview(
            model_list_frame,
            columns=model_columns,
            show="headings",
            selectmode="browse",
        )
        model_headings = {
            "number": "#",
            "vertices": "Vertices",
            "triangles": "Triangles",
            "stride": "Stride",
            "topology": "Topology",
            "details": "Validated layout / bounds",
        }
        model_widths = {
            "number": 42,
            "vertices": 75,
            "triangles": 75,
            "stride": 58,
            "topology": 105,
            "details": 420,
        }
        for column in model_columns:
            self.model_tree.heading(column, text=model_headings[column])
            self.model_tree.column(
                column, width=model_widths[column], anchor="w", stretch=True
            )
        model_scrollbar = ttk.Scrollbar(
            model_list_frame, orient="vertical", command=self.model_tree.yview
        )
        self.model_tree.configure(yscrollcommand=model_scrollbar.set)
        self.model_tree.pack(side="left", fill="both", expand=True)
        model_scrollbar.pack(side="right", fill="y")
        self.model_tree.bind("<<TreeviewSelect>>", self.on_model_select)

        resource_controls = ttk.Frame(self.resource_tab, padding=(3, 3, 3, 5))
        resource_controls.pack(fill="x")
        ttk.Button(
            resource_controls,
            text="Export Selected Raw",
            command=self.export_selected_resource,
        ).pack(side="left")
        ttk.Button(
            resource_controls,
            text="Import Selected Raw",
            command=self.import_selected_resource,
        ).pack(side="left", padx=(6, 0))
        ttk.Button(
            resource_controls,
            text="Open / Play",
            command=self.open_selected_resource_external,
        ).pack(side="left", padx=(6, 0))
        ttk.Button(
            resource_controls,
            text="Export All Resources",
            command=self.export_every_resource,
        ).pack(side="left", padx=(6, 0))
        ttk.Label(
            resource_controls,
            text="Unknown rows are byte-exact, unnamed 2K data",
        ).pack(side="left", padx=(8, 0))
        ttk.Label(resource_controls, text="Filter:").pack(side="left", padx=(10, 2))
        self.resource_filter_var = tk.StringVar()
        resource_filter = ttk.Entry(
            resource_controls, textvariable=self.resource_filter_var, width=18
        )
        resource_filter.pack(side="left", fill="x", expand=True)
        self.resource_filter_var.trace_add(
            "write", lambda *_arguments: self.refresh_resource_tree()
        )

        resource_list_frame = ttk.Frame(self.resource_tab)
        resource_list_frame.pack(fill="both", expand=True)
        resource_columns = (
            "number", "kind", "name", "extension", "offset", "size", "details"
        )
        self.resource_tree = ttk.Treeview(
            resource_list_frame,
            columns=resource_columns,
            show="headings",
            selectmode="browse",
        )
        resource_headings = {
            "number": "#",
            "kind": "Kind",
            "name": "Resource / exported name",
            "extension": "Extension",
            "offset": "Offset",
            "size": "Size",
            "details": "Details",
        }
        resource_widths = {
            "number": 42,
            "kind": 135,
            "name": 210,
            "extension": 72,
            "offset": 85,
            "size": 85,
            "details": 330,
        }
        for column in resource_columns:
            self.resource_tree.heading(column, text=resource_headings[column])
            self.resource_tree.column(
                column, width=resource_widths[column], anchor="w", stretch=True
            )
        resource_vscroll = ttk.Scrollbar(
            resource_list_frame, orient="vertical", command=self.resource_tree.yview
        )
        resource_hscroll = ttk.Scrollbar(
            resource_list_frame, orient="horizontal", command=self.resource_tree.xview
        )
        self.resource_tree.configure(
            yscrollcommand=resource_vscroll.set, xscrollcommand=resource_hscroll.set
        )
        self.resource_tree.grid(row=0, column=0, sticky="nsew")
        resource_vscroll.grid(row=0, column=1, sticky="ns")
        resource_hscroll.grid(row=1, column=0, sticky="ew")
        resource_list_frame.rowconfigure(0, weight=1)
        resource_list_frame.columnconfigure(0, weight=1)
        self.resource_tree.bind("<<TreeviewSelect>>", self.on_resource_select)

        catalog_controls = ttk.Frame(self.catalog_tab, padding=(3, 3, 3, 5))
        catalog_controls.pack(fill="x")
        ttk.Label(catalog_controls, text="Search every IFF:").pack(side="left")
        self.catalog_search_var = tk.StringVar()
        catalog_search = ttk.Entry(
            catalog_controls, textvariable=self.catalog_search_var, width=24
        )
        catalog_search.pack(side="left", fill="x", expand=True, padx=(4, 8))
        ttk.Label(catalog_controls, text="Kind:").pack(side="left")
        self.catalog_kind_var = tk.StringVar(value="All kinds")
        self.catalog_kind_combo = ttk.Combobox(
            catalog_controls,
            textvariable=self.catalog_kind_var,
            values=("All kinds",),
            width=22,
            state="readonly",
        )
        self.catalog_kind_combo.pack(side="left", padx=(4, 8))
        ttk.Button(
            catalog_controls,
            text="Open Parent IFF",
            command=self.open_catalog_resource,
        ).pack(side="left")
        self.catalog_count_var = tk.StringVar(
            value="Build the catalog to list every IFF resource"
        )
        ttk.Label(
            self.catalog_tab, textvariable=self.catalog_count_var, padding=(4, 0, 4, 4)
        ).pack(fill="x")

        catalog_list_frame = ttk.Frame(self.catalog_tab)
        catalog_list_frame.pack(fill="both", expand=True)
        catalog_columns = (
            "iff", "number", "kind", "name", "extension", "offset", "size", "details"
        )
        self.catalog_tree = ttk.Treeview(
            catalog_list_frame,
            columns=catalog_columns,
            show="headings",
            selectmode="browse",
        )
        catalog_headings = {
            "iff": "IFF file",
            "number": "#",
            "kind": "Kind",
            "name": "Resource / exported name",
            "extension": "Extension",
            "offset": "Offset",
            "size": "Size",
            "details": "Details",
        }
        catalog_widths = {
            "iff": 210,
            "number": 42,
            "kind": 135,
            "name": 210,
            "extension": 72,
            "offset": 80,
            "size": 75,
            "details": 300,
        }
        for column in catalog_columns:
            self.catalog_tree.heading(column, text=catalog_headings[column])
            self.catalog_tree.column(
                column, width=catalog_widths[column], anchor="w", stretch=True
            )
        catalog_vscroll = ttk.Scrollbar(
            catalog_list_frame, orient="vertical", command=self.catalog_tree.yview
        )
        catalog_hscroll = ttk.Scrollbar(
            catalog_list_frame, orient="horizontal", command=self.catalog_tree.xview
        )
        self.catalog_tree.configure(
            yscrollcommand=catalog_vscroll.set, xscrollcommand=catalog_hscroll.set
        )
        self.catalog_tree.grid(row=0, column=0, sticky="nsew")
        catalog_vscroll.grid(row=0, column=1, sticky="ns")
        catalog_hscroll.grid(row=1, column=0, sticky="ew")
        catalog_list_frame.rowconfigure(0, weight=1)
        catalog_list_frame.columnconfigure(0, weight=1)
        self.catalog_tree.bind("<<TreeviewSelect>>", self.on_catalog_resource_select)
        self.catalog_tree.bind("<Double-1>", self.open_catalog_resource)
        self.catalog_search_var.trace_add(
            "write", lambda *_arguments: self.schedule_catalog_resource_refresh()
        )
        self.catalog_kind_combo.bind(
            "<<ComboboxSelected>>", lambda _event: self.refresh_catalog_resource_tree()
        )

        self.preview_label = tk.Label(
            right,
            text="Open an NBA 2K20 Android IFF file",
            bg="#222222",
            fg="white",
            compound="top",
            padx=8,
            pady=8,
        )
        self.preview_label.pack(fill="both", expand=True)
        self.info_label = ttk.Label(right, text="", padding=(4, 8), justify="left")
        self.info_label.pack(fill="x")
        self.status = ttk.Label(self.root, text="Ready", relief="sunken", anchor="w", padding=4)
        self.status.pack(fill="x", side="bottom")

        if self.mobile_ui:
            # Give the preview a fixed, predictable area on portrait phones.
            # 260 px is enough to display a 2048x1024 texture at its correct
            # 2:1 aspect ratio while preserving useful space for the texture list.
            def _set_mobile_preview_sash():
                try:
                    self.root.update_idletasks()
                    available = self._mobile_preview_pane.winfo_height()
                    target = min(320, max(220, available // 2))
                    self._mobile_preview_pane.sashpos(0, target)
                except Exception:
                    pass
            self.root.after(250, _set_mobile_preview_sash)
            self.root.after(900, _set_mobile_preview_sash)

        # Reflow the long desktop toolbars into touch-friendly rows on phones.
        # All original buttons remain the same widgets/commands, so no feature
        # is removed; this only changes their layout.
        if self.mobile_ui:
            def _grid_toolbar(frame, columns=4):
                children = frame.winfo_children()
                for child in children:
                    try:
                        child.pack_forget()
                    except Exception:
                        pass
                for column in range(columns):
                    frame.columnconfigure(column, weight=1, uniform="toolbar")
                for index, child in enumerate(children):
                    try:
                        if isinstance(child, ttk.Label) and (
                            child is self.file_label or child is self.obb_label_var
                        ):
                            continue
                    except Exception:
                        pass
                    row, column = divmod(index, columns)
                    child.grid(row=row, column=column, sticky="nsew", padx=2, pady=2)

            _grid_toolbar(toolbar, 2)
            _grid_toolbar(obb_toolbar, 2)

            def _grid_controls(frame, columns=3):
                children = frame.winfo_children()
                for child in children:
                    try:
                        child.pack_forget()
                    except Exception:
                        pass
                for column in range(columns):
                    frame.columnconfigure(column, weight=1, uniform="controls")
                for index, child in enumerate(children):
                    row, column = divmod(index, columns)
                    try:
                        child.grid(row=row, column=column, sticky="ew", padx=2, pady=2)
                    except Exception:
                        pass

            for _controls in (
                file_controls,
                texture_controls,
                model_controls,
                resource_controls,
                catalog_controls,
            ):
                _grid_controls(_controls, 2)

            # Keep the main search/filter fields usable on narrow screens.
            try:
                filter_entry.configure(width=12)
                resource_filter.configure(width=12)
                catalog_search.configure(width=12)
            except Exception:
                pass

            # The tab labels and list headings are deliberately compact on phones.
            try:
                self.detail_notebook.configure(padding=0)
            except Exception:
                pass

            # The status/OBB text should have enough width and stay readable.
            for frame in (toolbar, obb_toolbar):
                frame.configure(padding=2)

        if initial is not None:
            self.root.after(50, lambda: self.load_path(initial))

    def choose_file(self) -> None:
        if not self.confirm_discard_changes():
            return
        selected = self.filedialog.askopenfilename(
            title="Open NBA 2K20 Android IFF",
            filetypes=(("NBA 2K IFF", "*.iff *.IFF *.decompressed"), ("All files", "*.*")),
        )
        if selected:
            self.load_path(Path(selected))

    def choose_obb(self) -> None:
        if self.obb_save_thread is not None and self.obb_save_thread.is_alive():
            self.messagebox.showinfo("OBB save", "Wait for the current OBB save to finish.")
            return
        if not self.confirm_discard_changes():
            return
        if self.obb_session is not None and self.obb_session.staged:
            if not self.messagebox.askyesno(
                "Discard staged OBB edits?",
                "Opening another OBB will discard IFF entries staged for the current "
                "OBB but not yet saved. Continue?",
            ):
                return
        selected = self.filedialog.askopenfilename(
            title="Open NBA 2K20 main or patch OBB",
            filetypes=(("NBA 2K OBB", "*.obb"), ("All files", "*.*")),
        )
        if not selected:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Reading OBB table from {selected} ...")
        self.root.update_idletasks()
        try:
            cache_dir = Path(self.external_temp.name) / "obb_edits"
            session = DirectObbSession(Path(selected), cache_dir)
            rows = session.rows()
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Cannot open OBB", str(error))
            self.status.configure(text="OBB open failed")
            return
        finally:
            self.root.configure(cursor="")
        self.obb_session = session
        self.obb_rows = rows
        self.visible_obb_rows = rows
        self.obb_iff_rows = [row for row in rows if row[8]]
        self.visible_obb_iff_rows = self.obb_iff_rows
        self.obb_entry_results = {}
        self.obb_current_index = None
        self.file_source_mode = "obb"
        self.filter_var.set("")
        self.catalog_button.configure(state="disabled")
        self.catalog_cancel_button.configure(state="disabled")
        self.refresh_file_tree()
        self.refresh_catalog_resource_tree()
        self.refresh_obb_controls()
        self.status.configure(
            text=(
                f"Opened {session.path.name}: {len(self.obb_iff_rows):,} editable IFF "
                f"entries listed from {len(rows):,} total archive entries"
            )
        )

    def refresh_obb_controls(self) -> None:
        if self.obb_session is None:
            self.obb_label_var.set("No OBB opened")
            self.obb_browse_button.configure(state="disabled")
            self.obb_export_iff_button.configure(state="disabled")
            self.obb_import_iff_button.configure(state="disabled")
            self.obb_save_button.configure(state="disabled")
            self.obb_save_copy_button.configure(state="disabled")
            return
        staged = len(self.obb_session.staged)
        self.obb_label_var.set(
            f"{self.obb_session.path.name} | {len(self.obb_session.obb.entries):,} entries | "
            f"{staged} edited"
        )
        saving = self.obb_save_thread is not None and self.obb_save_thread.is_alive()
        self.obb_browse_button.configure(state="disabled" if saving else "normal")
        current_state = (
            "normal"
            if self.obb_current_index is not None and not saving
            else "disabled"
        )
        self.obb_export_iff_button.configure(state=current_state)
        self.obb_import_iff_button.configure(state=current_state)
        # Let the Save buttons stay usable while an OBB entry is open.
        # Save OBB will stage a dirty entry automatically before rebuilding,
        # so disabling these buttons merely because `staged == 0` made them
        # appear permanently grey on Android/Pydroid.
        can_save = (
            self.obb_current_index is not None
            or staged > 0
        ) and not saving
        save_state = "normal" if can_save else "disabled"
        self.obb_save_button.configure(state=save_state)
        self.obb_save_copy_button.configure(state=save_state)

    def show_obb_browser(self) -> None:
        if self.obb_session is None:
            self.messagebox.showinfo("OBB entries", "Open an NBA 2K20 OBB first.")
            return
        if self.obb_browser is not None and self.obb_browser.winfo_exists():
            self.obb_browser.title(f"OBB Entries - {self.obb_session.path.name}")
            self.obb_browser.deiconify()
            self.obb_browser.lift()
            self.refresh_obb_browser()
            return
        ttk = self.ttk
        window = self.tk.Toplevel(self.root)
        self.obb_browser = window
        window.title(f"OBB Entries - {self.obb_session.path.name}")
        window.geometry("1120x680")
        window.minsize(850, 480)
        window.protocol("WM_DELETE_WINDOW", window.withdraw)
        controls = ttk.Frame(window, padding=8)
        controls.pack(fill="x")
        ttk.Label(controls, text="Search:").pack(side="left")
        self.obb_filter_var = self.tk.StringVar()
        ttk.Entry(controls, textvariable=self.obb_filter_var, width=35).pack(
            side="left", fill="x", expand=True, padx=(5, 8)
        )
        ttk.Button(controls, text="Open Selected IFF", command=self.open_obb_entry).pack(
            side="left"
        )
        self.obb_browser_count_var = self.tk.StringVar()
        ttk.Label(window, textvariable=self.obb_browser_count_var, padding=(8, 0, 8, 6)).pack(
            fill="x"
        )
        frame = ttk.Frame(window, padding=(8, 0, 8, 8))
        frame.pack(fill="both", expand=True)
        columns = ("index", "name", "hash", "type", "length", "slot", "block", "state")
        self.obb_tree = ttk.Treeview(
            frame, columns=columns, show="headings", selectmode="browse"
        )
        headings = {
            "index": "Entry",
            "name": "Known name / hash label",
            "hash": "Hash",
            "type": "Type",
            "length": "Logical size",
            "slot": "OBB slot",
            "block": "Block",
            "state": "State",
        }
        widths = {
            "index": 60,
            "name": 235,
            "hash": 90,
            "type": 105,
            "length": 95,
            "slot": 95,
            "block": 85,
            "state": 105,
        }
        for column in columns:
            self.obb_tree.heading(column, text=headings[column])
            self.obb_tree.column(column, width=widths[column], anchor="w")
        scrollbar = ttk.Scrollbar(frame, orient="vertical", command=self.obb_tree.yview)
        self.obb_tree.configure(yscrollcommand=scrollbar.set)
        self.obb_tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        self.obb_tree.bind("<Double-1>", self.open_obb_entry)
        self.obb_filter_var.trace_add(
            "write", lambda *_arguments: self.refresh_obb_browser()
        )
        self.refresh_obb_browser()

    def refresh_obb_browser(self) -> None:
        if (
            self.obb_session is None
            or self.obb_browser is None
            or not self.obb_browser.winfo_exists()
        ):
            return
        query = self.obb_filter_var.get().strip().lower()
        self.obb_rows = self.obb_session.rows()
        self.visible_obb_rows = [
            row
            for row in self.obb_rows
            if not query
            or query in str(row[0]).lower()
            or query in row[1].lower()
            or query in row[2].lower()
            or query in row[3].lower()
        ]
        for item in self.obb_tree.get_children():
            self.obb_tree.delete(item)
        for visible_index, row in enumerate(self.visible_obb_rows):
            index, label, hash_text, type_name, length, slot, block, staged, editable = row
            state = "EDITED" if staged else ("IFF editable" if editable else "raw entry")
            self.obb_tree.insert(
                "",
                "end",
                iid=str(visible_index),
                values=(
                    index,
                    label,
                    hash_text,
                    type_name,
                    readable_size(length),
                    readable_size(slot),
                    block,
                    state,
                ),
            )
        self.obb_browser_count_var.set(
            f"Showing {len(self.visible_obb_rows):,}/{len(self.obb_rows):,} entries. "
            "Compressed and zlib-image rows open directly in the IFF editor."
        )

    def selected_obb_row(self) -> tuple | None:
        if not hasattr(self, "obb_tree") or not self.obb_tree.selection():
            return None
        visible_index = int(self.obb_tree.selection()[0])
        if visible_index < 0 or visible_index >= len(self.visible_obb_rows):
            return None
        return self.visible_obb_rows[visible_index]

    def open_obb_entry(self, _event=None) -> None:
        row = self.selected_obb_row()
        if row is None or self.obb_session is None:
            self.messagebox.showinfo("OBB entry", "Select an OBB entry first.")
            return
        index, label, _hash, type_name, _length, _slot, _block, _staged, editable = row
        self.open_obb_entry_index(index, label, type_name, editable)

    def open_obb_entry_index(
        self, index: int, label: str, type_name: str, editable: bool = True
    ) -> None:
        if self.obb_session is None:
            return
        if not editable:
            self.messagebox.showinfo(
                "Raw OBB entry",
                f"Entry {index} is type {type_name}, not a compressed IFF entry. "
                "Direct raw-entry editing is not enabled in this version.",
            )
            return
        if not self.confirm_discard_changes():
            return
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Decompressing OBB entry {index}: {label} ...")
        self.root.update_idletasks()
        try:
            raw = self.obb_session.read_entry_raw(index)
            entry_dir = Path(self.external_temp.name) / "obb_entries"
            entry_dir.mkdir(parents=True, exist_ok=True)
            filename = label if label.lower().endswith(".iff") else f"{label}.iff"
            temporary_entry = entry_dir / f"{index:04d}_{filename}"
            temporary_entry.write_bytes(raw)
            self._load_path_sync(temporary_entry)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Cannot open OBB entry", str(error))
            self.status.configure(text="OBB entry open failed")
            return
        finally:
            self.root.configure(cursor="")
        self.obb_current_index = index
        if self.opened is not None:
            decodable = sum(
                texture.payload_offset is not None for texture in self.opened.textures
            )
            leaf_count = sum(
                not resource.container for resource in self.opened.resources
            )
            self.obb_entry_results[index] = (
                f"{decodable}/{len(self.opened.textures)} T | {leaf_count} R"
            )
        self.file_label.configure(text=f"[OBB #{index}] {label}")
        self.refresh_file_tree()
        self.refresh_obb_controls()
        self.status.configure(
            text=f"Editing OBB entry {index}; Save IFF stages it, then Save OBB rebuilds the archive"
        )
        self.root.lift()

    def export_current_obb_iff(self) -> None:
        if self.obb_session is None or self.obb_current_index is None:
            self.messagebox.showinfo(
                "Export IFF", "Open an editable IFF entry from an OBB first."
            )
            return
        index = self.obb_current_index
        expected_name = self.obb_session.entry_name(index)
        destination_text = self.filedialog.asksaveasfilename(
            title=f"Export complete OBB IFF entry #{index}",
            initialfile=expected_name,
            defaultextension=".iff",
            filetypes=(("NBA 2K IFF", "*.iff *.IFF"), ("All files", "*.*")),
        )
        if not destination_text:
            return
        destination = Path(destination_text)
        if destination.name.lower() != expected_name.lower():
            self.messagebox.showerror(
                "IFF filename must match",
                f"This OBB entry must be exported as:\n{expected_name}\n\n"
                f"Selected name:\n{destination.name}",
            )
            return
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Exporting complete IFF entry {expected_name} ...")
        self.root.update_idletasks()
        try:
            if self.dirty and self.opened is not None:
                raw, _mode, _changed_blocks = rebuild_compressed_iff(self.opened)
            else:
                raw = self.obb_session.read_entry_raw(index)
            verified = open_iff_bytes(raw, destination)
            temporary = destination.with_suffix(destination.suffix + ".partial")
            temporary.write_bytes(raw)
            os.replace(temporary, destination)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("IFF export failed", str(error))
            self.status.configure(text="Complete IFF export failed")
            return
        finally:
            self.root.configure(cursor="")
        self.status.configure(text=f"Exported and verified {expected_name}")
        self.messagebox.showinfo(
            "IFF exported",
            f"Complete IFF exported and verified:\n{destination}\n\n"
            f"Compressed container: {len(raw):,} bytes\n"
            f"Decompressed content: {len(verified.data):,} bytes",
        )

    def import_replace_current_obb_iff(self) -> None:
        if self.obb_session is None or self.obb_current_index is None:
            self.messagebox.showinfo(
                "Import / Replace IFF", "Open an editable IFF entry from an OBB first."
            )
            return
        if not self.confirm_discard_changes():
            return
        index = self.obb_current_index
        expected_name = self.obb_session.entry_name(index)
        source_text = self.filedialog.askopenfilename(
            title=f"Import replacement {expected_name}",
            filetypes=(("NBA 2K IFF", "*.iff *.IFF"), ("All files", "*.*")),
        )
        if not source_text:
            return
        source = Path(source_text)
        if source.name.lower() != expected_name.lower():
            self.messagebox.showerror(
                "IFF filename does not match",
                f"The selected OBB entry is:\n{expected_name}\n\n"
                f"The imported file is:\n{source.name}\n\n"
                "Select the same IFF filename to prevent replacing the wrong entry.",
            )
            return
        if not self.messagebox.askyesno(
            "Stage complete IFF replacement?",
            f"Replace OBB entry #{index} with this complete IFF?\n\n"
            f"Entry: {expected_name}\nReplacement: {source}\n\n"
            "The source OBB will not change until you click Save OBB.",
        ):
            return
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Validating replacement {expected_name} ...")
        self.root.update_idletasks()
        try:
            replacement_raw = source.read_bytes()
            legacy = detect_legacy_2k_wrapper(replacement_raw)
            if legacy is not None:
                ranges, import_mode = legacy
                # Older bootup IFFs are valid 94 EF 3B FF containers but do not
                # expose the newer ZLIB blocks.  Do not reject them merely
                # because the modern parser cannot decompress their legacy
                # container.  Validate the container partition and stage the
                # exact bytes as an opaque replacement.
                staged_raw = replacement_raw
                changed_blocks = len(ranges)
                staged = self.obb_session.stage_iff(
                    index, staged_raw, staged_raw, opaque_raw=True
                )
            else:
                replacement = open_iff_bytes(replacement_raw, source, look_for_manifest=True)
                baseline_raw = self.obb_session.read_entry_raw(index)
                baseline = open_iff_bytes(
                    baseline_raw,
                    Path(self.external_temp.name) / f"baseline_{index:04d}_{expected_name}",
                )
                if len(replacement.data) != len(baseline.data):
                    raise ValueError(
                        f"decompressed replacement size is {len(replacement.data):,} bytes; "
                        f"{expected_name} requires exactly {len(baseline.data):,} bytes"
                    )
                if replacement.wrapper_info is None:
                    baseline.data[:] = replacement.data
                    staged_raw, import_mode, changed_blocks = rebuild_compressed_iff(baseline)
                else:
                    staged_raw = replacement.source_raw
                    import_mode = replacement.wrapper
                    changed_blocks = len(replacement.wrapper_info.blocks)
                staged = self.obb_session.stage_iff(
                    index, staged_raw, bytes(replacement.data)
                )
            self.dirty = False
            self.changes = []
            _marker, type_name = self.obb_session.entry_type(index)
            self.open_obb_entry_index(index, staged.label, type_name, True)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("IFF replacement failed", str(error))
            self.status.configure(text="Complete IFF replacement failed")
            return
        finally:
            self.root.configure(cursor="")
        self.refresh_obb_controls()
        self.refresh_obb_browser()
        self.refresh_file_tree()
        self.status.configure(
            text=f"Staged complete replacement for {expected_name}; use Save OBB next"
        )
        self.messagebox.showinfo(
            "IFF replacement staged",
            f"Validated and staged:\n{expected_name}\n\n"
            f"Mode: {import_mode}\n"
            f"Container blocks: {changed_blocks}\n"
            f"Staged size: {staged.raw_size:,} bytes\n\n"
            "Click Save OBB or Save OBB Copy to rebuild and verify the archive.",
        )

    def confirm_discard_changes(self) -> bool:
        return not self.dirty or self.messagebox.askyesno(
            "Unsaved IFF changes",
            "The current IFF has unsaved texture/raw imports. Switch files and discard them?",
        )

    def choose_folder(self) -> None:
        selected = self.filedialog.askdirectory(
            title="Choose an extracted folder containing NBA 2K IFF files"
        )
        if not selected:
            return
        folder = Path(selected)
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Listing IFF files in {folder} ...")
        self.root.update_idletasks()
        try:
            files = find_iff_files(folder)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Cannot open folder", str(error))
            self.status.configure(text="Folder scan failed")
            return
        finally:
            self.root.configure(cursor="")
        self.folder_root = folder.resolve()
        self.folder_files = files
        self.file_source_mode = "folder"
        self.catalog_button.configure(state="normal")
        self.file_results = catalog_file_results(self.folder_root)
        self.filter_var.set("")
        self.refresh_file_tree()
        self.refresh_catalog_resource_tree()
        self.status.configure(
            text=(
                f"Listed {len(files):,} IFF files; "
                f"{len(self.file_results):,} have cached catalog records"
            )
        )
        if not files:
            self.messagebox.showinfo("No IFF files", f"No .iff files were found in:\n{folder}")

    def start_catalog(self) -> None:
        if self.file_source_mode != "folder" or self.folder_root is None:
            self.messagebox.showinfo(
                "IFF contents catalog", "Open an extracted IFF folder first."
            )
            return
        if self.catalog_thread is not None and self.catalog_thread.is_alive():
            return
        while True:
            try:
                self.catalog_queue.get_nowait()
            except queue.Empty:
                break
        self.catalog_cancel.clear()
        self.catalog_button.configure(state="disabled")
        self.catalog_cancel_button.configure(state="normal")
        folder = self.folder_root
        self.status.configure(
            text=(
                f"Building resumable contents catalog for {len(self.folder_files):,} IFFs ..."
            )
        )

        def report(index, total, path, outcome, error_text) -> None:
            self.catalog_queue.put(
                ("progress", index, total, str(path), outcome, error_text)
            )

        def worker() -> None:
            try:
                result = build_folder_catalog(
                    folder,
                    progress=report,
                    cancel_event=self.catalog_cancel,
                )
                self.catalog_queue.put(("complete", result))
            except Exception as error:  # noqa: BLE001
                self.catalog_queue.put(("fatal", str(error)))

        self.catalog_thread = threading.Thread(
            target=worker, name="nba2k20-iff-catalog", daemon=True
        )
        self.catalog_thread.start()
        self.root.after(100, self.poll_catalog)

    def cancel_catalog(self) -> None:
        if self.catalog_thread is not None and self.catalog_thread.is_alive():
            self.catalog_cancel.set()
            self.catalog_cancel_button.configure(state="disabled")
            self.status.configure(text="Stopping catalog safely after the current IFF ...")

    def poll_catalog(self) -> None:
        complete = None
        fatal = None
        latest = None
        while True:
            try:
                message = self.catalog_queue.get_nowait()
            except queue.Empty:
                break
            if message[0] == "progress":
                latest = message
            elif message[0] == "complete":
                complete = message[1]
            elif message[0] == "fatal":
                fatal = message[1]
        if latest is not None:
            _, index, total, path_text, outcome, error_text = latest
            suffix = f"; error: {error_text}" if error_text else ""
            self.status.configure(
                text=(
                    f"Catalog {index:,}/{total:,}: {Path(path_text).name} "
                    f"({outcome}){suffix}"
                )
            )
        if complete is not None or fatal is not None:
            self.catalog_button.configure(state="normal")
            self.catalog_cancel_button.configure(state="disabled")
            self.catalog_thread = None
            if fatal is not None:
                self.status.configure(text="Catalog build failed")
                self.messagebox.showerror("IFF catalog failed", fatal)
                return
            assert self.folder_root is not None
            self.file_results = catalog_file_results(self.folder_root)
            self.refresh_file_tree()
            self.refresh_catalog_resource_tree()
            state = "cancelled safely" if complete["cancelled"] else "complete"
            self.status.configure(
                text=(
                    f"Catalog {state}: {complete['scanned']:,} scanned, "
                    f"{complete['cached']:,} cached, {complete['errors']:,} errors"
                )
            )
            self.messagebox.showinfo(
                "IFF contents catalog",
                f"Catalog {state}.\n\n"
                f"Files: {complete['file_count']:,}\n"
                f"New/changed scans: {complete['scanned']:,}\n"
                f"Already cached: {complete['cached']:,}\n"
                f"Errors: {complete['errors']:,}\n"
                f"Elapsed: {complete['elapsed_seconds']:.1f} seconds\n\n"
                f"Database:\n{complete['database']}",
            )
            return
        if self.catalog_thread is not None and self.catalog_thread.is_alive():
            self.root.after(120, self.poll_catalog)

    def sort_file_list(self, column: str) -> None:
        """Sort the folder/OBB IFF list by the clicked visible column."""

        if column not in {"name", "size", "folder", "result"}:
            return
        if self.file_sort_column == column:
            self.file_sort_descending = not self.file_sort_descending
        else:
            self.file_sort_column = column
            # The most useful first size view is largest-to-smallest. Text
            # columns begin A-to-Z and toggle direction on the next click.
            self.file_sort_descending = column == "size"
        self.refresh_file_tree()

    def update_file_headings(self) -> None:
        if not hasattr(self, "file_tree"):
            return
        headings = {
            "name": "IFF file",
            "size": "Stored size" if self.file_source_mode == "obb" else "Size",
            "folder": "OBB entry" if self.file_source_mode == "obb" else "Relative folder",
            "result": "Contents",
        }
        for column, label in headings.items():
            if self.file_sort_column == column:
                label += " ▼" if self.file_sort_descending else " ▲"
            self.file_tree.heading(column, text=label)

    def sort_visible_file_rows(self) -> None:
        column = self.file_sort_column
        if column is None:
            return
        reverse = self.file_sort_descending
        if self.file_source_mode == "obb" and self.obb_session is not None:
            def obb_key(row):
                if column == "name":
                    return (row[1].casefold(), row[0])
                if column == "size":
                    return (int(row[5]), row[0])
                if column == "folder":
                    return (str(row[3]).casefold(), int(row[6]), row[0])
                result = self.obb_entry_results.get(row[0], "")
                if row[7]:
                    result = "EDITED " + result
                return (result.casefold(), row[0])

            self.visible_obb_iff_rows.sort(key=obb_key, reverse=reverse)
            return
        if self.folder_root is None:
            return

        def folder_key(path: Path):
            relative = path.relative_to(self.folder_root)
            if column == "name":
                return (path.name.casefold(), str(relative).casefold())
            if column == "size":
                return (path.stat().st_size, str(relative).casefold())
            if column == "folder":
                return (str(relative.parent).casefold(), path.name.casefold())
            return (self.file_results.get(path, "").casefold(), str(relative).casefold())

        self.visible_files.sort(key=folder_key, reverse=reverse)

    def refresh_file_tree(self) -> None:
        if not hasattr(self, "file_tree"):
            return
        query = self.filter_var.get().strip().lower()
        if self.file_source_mode == "obb" and self.obb_session is not None:
            self.obb_rows = self.obb_session.rows()
            self.obb_iff_rows = [row for row in self.obb_rows if row[8]]
            self.visible_obb_iff_rows = [
                row
                for row in self.obb_iff_rows
                if not query
                or query in str(row[0]).lower()
                or query in row[1].lower()
                or query in row[2].lower()
                or query in row[3].lower()
            ]
            self.visible_files = []
            self.sort_visible_file_rows()
            self.update_file_headings()
            self.suppress_file_event = True
            try:
                for item in self.file_tree.get_children():
                    self.file_tree.delete(item)
                for visible_index, row in enumerate(self.visible_obb_iff_rows):
                    (
                        entry_index,
                        label,
                        _hash_text,
                        type_name,
                        length,
                        slot,
                        block,
                        staged,
                        _editable,
                    ) = row
                    filename = label if label.lower().endswith(".iff") else f"{label}.iff"
                    result = self.obb_entry_results.get(entry_index, "")
                    if staged:
                        result = "EDITED" + (f" | {result}" if result else "")
                    self.file_tree.insert(
                        "",
                        "end",
                        iid=str(visible_index),
                        values=(
                            f"{entry_index:04d}_{filename}",
                            readable_size(slot),
                            (
                                f"#{entry_index} | {type_name} | block {block} | "
                                f"logical {readable_size(length)}"
                            ),
                            result,
                        ),
                    )
                if self.obb_current_index is not None:
                    for visible_index, row in enumerate(self.visible_obb_iff_rows):
                        if row[0] == self.obb_current_index:
                            iid = str(visible_index)
                            self.file_tree.selection_set(iid)
                            self.file_tree.focus(iid)
                            self.file_tree.see(iid)
                            break
            finally:
                self.suppress_file_event = False
            self.folder_label_var.set(
                f"OBB IFF files: {len(self.visible_obb_iff_rows):,}/{len(self.obb_iff_rows):,}"
            )
            return

        resource_matches = (
            catalog_matching_files(self.folder_root, query)
            if self.folder_root is not None and query
            else set()
        )
        if self.folder_root is None:
            self.visible_files = []
        else:
            self.visible_files = [
                path
                for path in self.folder_files
                if not query
                or query in path.name.lower()
                or query in str(path.relative_to(self.folder_root)).lower()
                or path in resource_matches
            ]
        self.sort_visible_file_rows()
        self.update_file_headings()
        self.suppress_file_event = True
        try:
            for item in self.file_tree.get_children():
                self.file_tree.delete(item)
            for index, path in enumerate(self.visible_files):
                relative = path.relative_to(self.folder_root)
                folder_text = "" if str(relative.parent) == "." else str(relative.parent)
                self.file_tree.insert(
                    "",
                    "end",
                    iid=str(index),
                    values=(
                        path.name,
                        readable_size(path.stat().st_size),
                        folder_text,
                        self.file_results.get(path, ""),
                    ),
                )
            if self.opened and self.opened.path in self.visible_files:
                index = self.visible_files.index(self.opened.path)
                self.file_tree.selection_set(str(index))
                self.file_tree.focus(str(index))
                self.file_tree.see(str(index))
        finally:
            self.suppress_file_event = False
        if self.folder_root is not None:
            self.folder_label_var.set(
                f"IFF files: {len(self.visible_files):,}/{len(self.folder_files):,}"
            )

    def schedule_catalog_resource_refresh(self) -> None:
        if self.catalog_filter_after_id is not None:
            self.root.after_cancel(self.catalog_filter_after_id)
        self.catalog_filter_after_id = self.root.after(
            220, self._run_scheduled_catalog_resource_refresh
        )

    def _run_scheduled_catalog_resource_refresh(self) -> None:
        self.catalog_filter_after_id = None
        self.refresh_catalog_resource_tree()

    def refresh_catalog_resource_tree(self) -> None:
        """Populate one searchable view spanning resources from every IFF."""

        if not hasattr(self, "catalog_tree"):
            return
        for item in self.catalog_tree.get_children():
            self.catalog_tree.delete(item)
        self.catalog_rows = []
        if self.file_source_mode == "obb":
            self.catalog_count_var.set(
                "Direct OBB mode lists IFFs above; open an entry to inspect all of its resources."
            )
            return
        if self.folder_root is None:
            self.catalog_count_var.set("Open an extracted IFF folder first")
            return
        database = catalog_path_for(self.folder_root)
        if not database.is_file():
            self.catalog_kind_combo.configure(values=("All kinds",))
            self.catalog_kind_var.set("All kinds")
            self.catalog_count_var.set(
                "No catalog yet - click Build/Update Catalog above"
            )
            return
        try:
            kinds = catalog_resource_kinds(self.folder_root)
            current_kind = self.catalog_kind_var.get()
            values = ("All kinds", *kinds)
            self.catalog_kind_combo.configure(values=values)
            if current_kind not in values:
                current_kind = "All kinds"
                self.catalog_kind_var.set(current_kind)
            rows, total = catalog_resource_rows(
                self.folder_root,
                query_text=self.catalog_search_var.get(),
                kind=current_kind,
            )
        except sqlite3.Error as error:
            self.catalog_count_var.set(f"Catalog is busy: {error}")
            return
        self.catalog_rows = rows
        for index, row in enumerate(rows):
            relative, number, kind, name, offset, size, extension, details, _confidence, _texture = row
            self.catalog_tree.insert(
                "",
                "end",
                iid=str(index),
                values=(
                    relative,
                    number,
                    kind,
                    name,
                    extension or ".bin",
                    f"0x{offset:X}",
                    readable_size(size),
                    details,
                ),
            )
        shown = len(rows)
        suffix = "" if shown == total else f"; showing first {shown:,}"
        self.catalog_count_var.set(
            f"Folder-wide matches: {total:,}{suffix}. Double-click a row to open its parent IFF."
        )

    def selected_catalog_resource(self) -> tuple | None:
        if not self.catalog_tree.selection():
            return None
        index = int(self.catalog_tree.selection()[0])
        if index < 0 or index >= len(self.catalog_rows):
            return None
        return self.catalog_rows[index]

    def on_catalog_resource_select(self, _event=None) -> None:
        row = self.selected_catalog_resource()
        if row is None:
            return
        relative, number, kind, name, offset, size, extension, details, confidence, texture = row
        self.preview_photo = None
        self.preview_label.configure(
            image="",
            text=(
                f"{name}\n\n"
                f"Parent IFF: {relative}\n"
                f"Resource: #{number}   Kind: {kind}\n"
                f"Offset: 0x{offset:X}   Size: {size:,} bytes   Extension: {extension or '(raw)'}\n"
                f"Detection: {confidence}\n"
                f"Texture number: {texture if texture is not None else '-'}\n\n"
                f"{details}\n\n"
                "Double-click this row to open the parent IFF and jump to the resource."
            ),
            font=("Consolas", 11 if self.mobile_ui else 9),
            anchor="nw",
            justify="left",
        )
        self.status.configure(text=f"Catalog resource #{number} in {relative}")

    def open_catalog_resource(self, _event=None) -> None:
        row = self.selected_catalog_resource()
        if row is None or self.folder_root is None:
            self.messagebox.showinfo(
                "All IFF Contents", "Select a catalog resource row first."
            )
            return
        relative, number = row[0], row[1]
        path = (self.folder_root / relative).resolve()
        if self.opened is None or self.opened.path != path:
            if not self.confirm_discard_changes():
                return
            self._load_path_sync(path)
        if self.opened is None:
            return
        self.resource_filter_var.set("")
        self.detail_notebook.select(self.resource_tab)
        iid = str(number - 1)
        if self.resource_tree.exists(iid):
            self.resource_tree.selection_set(iid)
            self.resource_tree.focus(iid)
            self.resource_tree.see(iid)
            self.on_resource_select()

    def schedule_file_refresh(self) -> None:
        if self.filter_after_id is not None:
            self.root.after_cancel(self.filter_after_id)
        self.filter_after_id = self.root.after(180, self._run_scheduled_refresh)

    def _run_scheduled_refresh(self) -> None:
        self.filter_after_id = None
        # Refreshing the Treeview can steal keyboard focus from the Search entry.
        # Remember whether Search had focus before rebuilding the list and restore
        # it afterwards so typing can continue across multiple searches/keystrokes.
        search_has_focus = (
            hasattr(self, "filter_entry")
            and self.root.focus_get() == self.filter_entry
        )
        self.refresh_file_tree()
        if search_has_focus and self.filter_entry.winfo_exists():
            self.filter_entry.focus_set()

    def update_file_result(self, path: Path, result: str) -> None:
        if self.file_source_mode == "obb":
            return
        resolved = path.resolve()
        self.file_results[resolved] = result
        if resolved in self.visible_files:
            index = self.visible_files.index(resolved)
            if self.file_tree.exists(str(index)):
                self.file_tree.set(str(index), "result", result)

    def on_file_select(self, _event=None) -> None:
        if self.suppress_file_event or not self.file_tree.selection():
            return
        index = int(self.file_tree.selection()[0])
        if self.file_source_mode == "obb":
            if index < 0 or index >= len(self.visible_obb_iff_rows):
                return
            row = self.visible_obb_iff_rows[index]
            entry_index, label, _hash, type_name = row[:4]
            if self.obb_current_index == entry_index and self.opened is not None:
                return
            self.open_obb_entry_index(entry_index, label, type_name, row[8])
            return
        if index < 0 or index >= len(self.visible_files):
            return
        path = self.visible_files[index]
        if self.opened and path == self.opened.path:
            return
        if not self.confirm_discard_changes():
            self.suppress_file_event = True
            try:
                self.file_tree.selection_remove(*self.file_tree.selection())
                if self.opened and self.opened.path in self.visible_files:
                    current = self.visible_files.index(self.opened.path)
                    self.file_tree.selection_set(str(current))
                    self.file_tree.focus(str(current))
            finally:
                self.suppress_file_event = False
            return
        self.load_path(path)

    def move_file(self, direction: int) -> None:
        if self.file_source_mode == "obb":
            if not self.visible_obb_iff_rows:
                self.messagebox.showinfo("OBB IFF files", "Open an OBB containing IFF entries first.")
                return
            current = None
            if self.obb_current_index is not None:
                for position, row in enumerate(self.visible_obb_iff_rows):
                    if row[0] == self.obb_current_index:
                        current = position
                        break
            if current is None:
                target = 0 if direction >= 0 else len(self.visible_obb_iff_rows) - 1
            else:
                target = (current + direction) % len(self.visible_obb_iff_rows)
            iid = str(target)
            self.file_tree.selection_set(iid)
            self.file_tree.focus(iid)
            self.file_tree.see(iid)
            self.open_obb_entry_index(
                self.visible_obb_iff_rows[target][0],
                self.visible_obb_iff_rows[target][1],
                self.visible_obb_iff_rows[target][3],
                self.visible_obb_iff_rows[target][8],
            )
            return
        if not self.visible_files:
            self.messagebox.showinfo("IFF folder", "Open a folder containing IFF files first.")
            return
        if self.opened and self.opened.path in self.visible_files:
            current = self.visible_files.index(self.opened.path)
            target = (current + direction) % len(self.visible_files)
        else:
            target = 0 if direction >= 0 else len(self.visible_files) - 1
        self.file_tree.selection_set(str(target))
        self.file_tree.focus(str(target))
        self.file_tree.see(str(target))

    def _load_path_sync(self, path: Path) -> None:
        """Synchronous loader for workflows that immediately need the parsed IFF."""
        path = path.resolve()
        self.open_generation += 1
        generation = self.open_generation
        if not path.is_file():
            raise ValueError(f"IFF file was not found: {path}")
        opened = open_iff(path)
        self._finish_load(path, opened, generation)

    def load_path(self, path: Path) -> None:
        """Open an IFF off the Tk main thread so large files do not freeze Android/Pydroid."""
        path = path.resolve()
        self.obb_current_index = None
        self.open_generation += 1
        generation = self.open_generation
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Opening {path.name} ...")
        self.root.update_idletasks()

        def worker() -> None:
            try:
                opened = open_iff(path)
                self.open_queue.put(("complete", generation, path, opened))
            except Exception as error:  # noqa: BLE001
                self.open_queue.put(("error", generation, path, str(error)))

        self.open_thread = threading.Thread(
            target=worker,
            name="nba2k20-iff-open",
            daemon=True,
        )
        self.open_thread.start()
        self.root.after(50, self.poll_open)

    def poll_open(self) -> None:
        latest = None
        while True:
            try:
                latest = self.open_queue.get_nowait()
            except queue.Empty:
                break

        if latest is not None:
            kind, generation, path, payload = latest
            if generation == self.open_generation:
                self.open_thread = None
                if kind == "error":
                    self.root.configure(cursor="")
                    self.messagebox.showerror("Cannot open IFF", payload)
                    self.update_file_result(path, "ERROR")
                    self.status.configure(text="Open failed")
                else:
                    self._finish_load(path, payload, generation)
                return

        if self.open_thread is not None and self.open_thread.is_alive():
            self.root.after(60, self.poll_open)

    def _ensure_deep_analysis(self, *, resources: bool = False, models: bool = False) -> None:
        """Load expensive inventories only when the user asks for them."""
        if self.opened is None:
            return
        opened = self.opened
        if models and not opened.deep_analysis_loaded:
            self.status.configure(text="Analyzing 3D model streams...")
            self.root.update_idletasks()
            opened.gpu_buffers = locate_gpu_buffers(
                bytes(opened.data), opened.block_sizes, opened.textures
            )
            opened.meshes = locate_meshes(
                bytes(opened.data), opened.block_sizes, opened.gpu_buffers
            )
            opened.deep_analysis_loaded = True
        if resources and not opened.resource_analysis_loaded:
            self.status.configure(text="Building resource map...")
            self.root.update_idletasks()
            if not opened.deep_analysis_loaded:
                opened.gpu_buffers = locate_gpu_buffers(
                    bytes(opened.data), opened.block_sizes, opened.textures
                )
                opened.deep_analysis_loaded = True
            opened.resources = locate_resources(
                bytes(opened.data),
                opened.block_sizes,
                opened.textures,
                opened.gpu_buffers,
            )
            opened.resource_analysis_loaded = True

    def _on_detail_tab_changed(self, _event=None) -> None:
        if self.opened is None:
            return
        selected = self.detail_notebook.select()
        if selected == str(self.model_tab):
            self._ensure_deep_analysis(models=True)
            self.refresh_model_tree()
        elif selected == str(self.resource_tab):
            self._ensure_deep_analysis(resources=True)
            self.refresh_resource_tree()

    def refresh_model_tree(self) -> None:
        if not hasattr(self, "model_tree"):
            return
        for item in self.model_tree.get_children():
            self.model_tree.delete(item)
        if self.opened is None:
            return
        for mesh in self.opened.meshes:
            self.model_tree.insert(
                "",
                "end",
                iid=str(mesh.number - 1),
                values=(
                    mesh.number,
                    f"{mesh.vertex_count:,}",
                    f"{mesh.triangle_count:,}",
                    mesh.vertex_stride,
                    mesh.topology,
                    f"{mesh.confidence}; {mesh.details}",
                ),
            )

    def _finish_load(self, path: Path, opened: OpenedIff, generation: int) -> None:
        if generation != self.open_generation:
            return
        self.root.configure(cursor="")
        self.opened = opened
        self.dirty = False
        self.changes = []
        self.preview_photo = None
        self.preview_label.configure(
            image="",
            text="Select a texture or an All Resources row",
            font="TkDefaultFont",
            anchor="center",
            justify="center",
        )
        for item in self.tree.get_children():
            self.tree.delete(item)
        for texture in opened.textures:
            payload_text = texture.location
            if texture.label:
                payload_text = f"{texture.label} | {payload_text}"
            self.tree.insert(
                "",
                "end",
                iid=str(texture.number - 1),
                values=(
                    texture.number,
                    texture_filename(texture),
                    f"{texture.width} x {texture.height}",
                    FORMAT_NAMES[texture.format_id],
                    payload_text + (" | full mip chain" if texture.uses_mip_chain else " | base level"),
                    f"{texture.texture_hash:08X}" if texture.has_header else "streamed",
                ),
            )
        for item in self.model_tree.get_children():
            self.model_tree.delete(item)
        self.resource_filter_var.set("")
        self.refresh_resource_tree()
        self.file_label.configure(text=opened.path.name)
        self.info_label.configure(
            text=(
                f"{opened.wrapper} | source {opened.source_size:,} bytes | "
                f"decoded {len(opened.data):,} bytes\n"
                f"Blocks: {', '.join(f'{size:,}' for size in opened.block_sizes)} | "
                f"boundary source: {opened.boundary_source}"
            )
        )
        decodable = sum(texture.payload_offset is not None for texture in opened.textures)
        leaf_count = sum(not resource.container for resource in opened.resources)
        self.update_file_result(
            opened.path,
            f"{decodable}/{len(opened.textures)} T | {len(opened.meshes)} M | {leaf_count} R",
        )
        self.status.configure(
            text=(
                f"Found {len(opened.textures)} supported texture resource(s), "
                f"{decodable} previewable; 3D models/resources load on demand"
            )
        )
        if opened.textures:
            self.detail_notebook.select(self.texture_tab)
            self.tree.selection_set("0")
            self.tree.focus("0")
        else:
            self.detail_notebook.select(self.resource_tab)
            self.preview_label.configure(
                text=(
                    "No supported texture headers were found.\n\n"
                    "Use the All Resources tab to inspect models, animation, audio, "
                    "shaders, or unclassified serialized data."
                )
            )
            if opened.resources:
                self.resource_tree.selection_set("0")
                self.resource_tree.focus("0")

    def refresh_resource_tree(self) -> None:
        if not hasattr(self, "resource_tree"):
            return
        query = self.resource_filter_var.get().strip().lower()
        selected_number = None
        if self.resource_tree.selection():
            selected_number = self.resource_tree.selection()[0]
        for item in self.resource_tree.get_children():
            self.resource_tree.delete(item)
        if not self.opened:
            return
        for resource in self.opened.resources:
            searchable = " ".join(
                (
                    resource.kind,
                    resource.name,
                    resource.extension,
                    resource.details,
                    resource.confidence,
                )
            ).lower()
            if query and query not in searchable:
                continue
            iid = str(resource.number - 1)
            self.resource_tree.insert(
                "",
                "end",
                iid=iid,
                values=(
                    resource.number,
                    resource.kind,
                    resource.name,
                    resource.extension or ".bin",
                    f"0x{resource.offset:X}",
                    readable_size(resource.size),
                    resource.details,
                ),
            )
        if selected_number is not None and self.resource_tree.exists(selected_number):
            self.resource_tree.selection_set(selected_number)
            self.resource_tree.focus(selected_number)

    def import_selected(self) -> None:
        texture = self.selected_texture()
        if not self.opened or texture is None:
            self.messagebox.showinfo("Import edited PNG", "Select a texture first.")
            return
        selected = self.filedialog.askopenfilename(
            title=(
                f"Import edited {texture.width}x{texture.height} PNG for "
                f"texture #{texture.number}"
            ),
            filetypes=(("PNG image", "*.png"),),
        )
        if not selected:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Encoding edited texture ...")
        self.root.update_idletasks()
        try:
            change = import_png(self.opened, texture, Path(selected))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Import failed", str(error))
            self.status.configure(text="Import failed")
            return
        finally:
            self.root.configure(cursor="")
        self.changes.append(change)
        self.dirty = True
        self.file_label.configure(text=self.opened.path.name + " *")
        self.on_select()
        mip_note = " with regenerated mip levels" if texture.uses_mip_chain else ""
        linked_count = int(change.get("linked_payload_copies_replaced", 1))
        linked_note = (
            f"; updated {linked_count} linked IFF copies" if linked_count > 1 else ""
        )
        self.status.configure(
            text=(
                f"Imported texture #{texture.number}{mip_note}{linked_note}; "
                "use Save IFF or Save IFF Copy next"
            )
        )

    def import_all_exported(self) -> None:
        if not self.opened:
            self.messagebox.showinfo("Import all PNGs", "Open an IFF file first.")
            return
        selected = self.filedialog.askdirectory(
            title="Choose folder containing edited Export All PNG files"
        )
        if not selected:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Matching and encoding all exported PNG titles ...")
        self.root.update_idletasks()
        try:
            report = import_all_exported_pngs(self.opened, Path(selected))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror(
                "Batch PNG import failed",
                f"No texture was left partially imported.\n\n{error}",
            )
            self.status.configure(text="Batch PNG import failed; all prior IFF bytes restored")
            return
        finally:
            self.root.configure(cursor="")
        self.changes.extend(report["changes"])
        self.dirty = True
        self.file_label.configure(text=self.opened.path.name + " *")
        if self.selected_texture() is not None:
            self.on_select()
        notes = []
        if report["missing_count"]:
            missing = report["missing"]
            summary = "\n".join(f"- {name}" for name in missing[:10])
            if len(missing) > 10:
                summary += f"\n- ... and {len(missing) - 10} more"
            notes.append(f"Missing expected PNGs (not changed):\n{summary}")
        if report["ignored_png_count"]:
            notes.append(
                f"Ignored unrelated PNGs: {report['ignored_png_count']}"
            )
        message = (
            f"Imported {report['matched_count']} texture PNG(s) by exact exported "
            f"filename from:\n{selected}\n\n"
            "Use Save IFF or Save IFF Copy next."
        )
        linked_total = sum(
            max(0, int(change.get("linked_payload_copies_replaced", 1)) - 1)
            for change in report["changes"]
        )
        if linked_total:
            message += f"\n\nAlso updated {linked_total} linked runtime texture copy/copies."
        if notes:
            message += "\n\n" + "\n\n".join(notes)
        self.messagebox.showinfo("Batch PNG import complete", message)
        self.status.configure(
            text=(
                f"Imported {report['matched_count']} PNG(s) by exported title; "
                "use Save IFF or Save IFF Copy next"
            )
        )

    def save_current(self) -> None:
        """Verify and atomically replace the currently opened IFF."""

        if not self.opened:
            self.messagebox.showinfo("Save IFF", "Open an IFF file first.")
            return
        if self.obb_session is not None and self.obb_current_index is not None:
            self.stage_current_obb_entry()
            return
        if not self.dirty:
            self.messagebox.showinfo("Save IFF", "There are no unsaved changes.")
            return
        destination = self.opened.path
        if not self.messagebox.askyesno(
            "Overwrite current IFF?",
            "This will replace the currently opened IFF after rebuilding and "
            "verifying it.\n\n"
            f"File:\n{destination}\n\n"
            "Save directly to this file?",
        ):
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Rebuilding, verifying, and saving current IFF ...")
        self.root.update_idletasks()
        try:
            report = save_iff(self.opened, destination, allow_overwrite=True)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Save failed", str(error))
            self.status.configure(text="Save failed; current IFF was not replaced")
            return
        finally:
            self.root.configure(cursor="")
        self.dirty = False
        self.changes = []
        # Reload the file so later edits use the newly saved container as their
        # baseline and the visible resource list reflects the saved bytes.
        self.load_path(destination)
        self.status.configure(text=f"Saved over and verified {destination}")
        self.messagebox.showinfo(
            "IFF saved",
            f"Current IFF replaced and verified:\n{destination}\n\n"
            f"Container mode: {report['mode']}",
        )

    def stage_current_obb_entry(self) -> None:
        if (
            self.opened is None
            or self.obb_session is None
            or self.obb_current_index is None
        ):
            self.messagebox.showinfo("Stage OBB entry", "Open an IFF from an OBB first.")
            return
        index = self.obb_current_index
        if not self.dirty:
            if index in self.obb_session.staged:
                self.messagebox.showinfo(
                    "OBB entry staged",
                    f"Entry {index} is already staged. Use Save OBB next.",
                )
            else:
                self.messagebox.showinfo("Stage OBB entry", "There are no unsaved changes.")
            return
        self.root.configure(cursor="watch")
        self.status.configure(text=f"Rebuilding and staging OBB entry {index} ...")
        self.root.update_idletasks()
        try:
            rebuilt, mode, changed_blocks = rebuild_compressed_iff(self.opened)
            staged = self.obb_session.stage_iff(
                index, rebuilt, bytes(self.opened.data)
            )
            # Reopen the staged container so further edits use it as the baseline.
            temporary_entry = self.opened.path
            temporary_entry.write_bytes(rebuilt)
            self.dirty = False
            self.changes = []
            self.load_path(temporary_entry)
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Cannot stage OBB entry", str(error))
            self.status.configure(text="OBB entry staging failed")
            return
        finally:
            self.root.configure(cursor="")
        self.obb_current_index = index
        self.file_label.configure(text=f"[OBB #{index}] {staged.label}")
        self.refresh_obb_controls()
        self.refresh_obb_browser()
        self.refresh_file_tree()
        self.status.configure(
            text=(
                f"Staged OBB entry {index}: {changed_blocks} compressed block(s), "
                f"mode={mode}; use Save OBB next"
            )
        )

    def prepare_obb_save(self) -> bool:
        if self.obb_session is None:
            self.messagebox.showinfo("Save OBB", "Open an NBA 2K20 OBB first.")
            return False
        if self.dirty:
            if self.obb_current_index is None:
                self.messagebox.showinfo(
                    "Unsaved non-OBB IFF",
                    "Save or discard the currently opened standalone IFF before saving the OBB.",
                )
                return False
            self.stage_current_obb_entry()
            if self.dirty:
                return False
        if not self.obb_session.staged:
            self.messagebox.showinfo(
                "Save OBB", "No edited IFF entries are staged. Edit an OBB entry and click Save IFF first."
            )
            return False
        return True

    def save_current_obb(self) -> None:
        if not self.prepare_obb_save() or self.obb_session is None:
            return
        source = self.obb_session.path
        # Android 11+ normally blocks direct writes to Android/obb from Python
        # apps. Save OBB therefore exports an Android-safe copy to Download on
        # Android instead of failing late inside os.replace().
        if sys.platform.startswith("linux") and Path("/storage/emulated/0").exists():
            try:
                destination = self._android_download_dir() / (source.stem + "_modded.obb")
            except Exception as error:
                self.messagebox.showerror("Android storage", str(error))
                return
            if destination.exists():
                destination = self._unique_destination(destination)
            if not self.messagebox.askyesno(
                "Save OBB to Download",
                "Android may block direct replacement of files inside Android/obb.\n\n"
                "This button will build and verify the edited OBB, then save it to the "
                "shared Download folder. You can move it to the game's OBB folder "
                "with a file manager that supports Android storage access.\n\n"
                f"Output:\n{destination}\n\n"
                f"Edited entries: {len(self.obb_session.staged)}",
            ):
                return
            self.start_obb_save(destination, allow_overwrite=False)
            return
        destination = source
        if not self.messagebox.askyesno(
            "Overwrite current OBB?",
            "The manager will build and fully verify a temporary OBB, then replace "
            "the current archive atomically. Temporary free space approximately equal "
            "to this OBB is required.\n\n"
            f"OBB:\n{destination}\n\n"
            f"Edited entries: {len(self.obb_session.staged)}\n\n"
            "Save directly to this OBB?",
        ):
            return
        self.start_obb_save(destination, allow_overwrite=True)

    @staticmethod
    def _unique_destination(path: Path) -> Path:
        stem, suffix = path.stem, path.suffix
        for index in range(2, 1000):
            candidate = path.with_name(f"{stem}_{index}{suffix}")
            if not candidate.exists():
                return candidate
        raise OSError("Could not create a unique OBB output filename")

    def save_obb_copy(self) -> None:
        if not self.prepare_obb_save() or self.obb_session is None:
            return
        source = self.obb_session.path
        initial_dir = None
        if sys.platform.startswith("linux") and Path("/storage/emulated/0").exists():
            try:
                initial_dir = str(self._android_download_dir())
            except Exception:
                initial_dir = None
        dialog_kwargs = dict(
            title="Save rebuilt and verified OBB copy",
            defaultextension=".obb",
            initialfile=source.stem + "_modded.obb",
            filetypes=(("NBA 2K OBB", "*.obb"), ("All files", "*.*")),
        )
        if initial_dir:
            dialog_kwargs["initialdir"] = initial_dir
        destination_text = self.filedialog.asksaveasfilename(**dialog_kwargs)
        if not destination_text:
            return
        destination = Path(destination_text).resolve()
        try:
            self._destination_is_writable(destination)
        except Exception as error:
            self.messagebox.showerror(
                "Cannot write OBB here",
                f"Android/Pydroid cannot write to this folder:\n{destination.parent}\n\n"
                f"Reason: {error}\n\n"
                "Choose a normal shared-storage folder such as Download. "
                "Direct writes to Android/obb are commonly blocked by Android.",
            )
            return
        if destination == source:
            self.messagebox.showinfo(
                "Save OBB Copy", "Use Save OBB when you want to overwrite the current archive."
            )
            return
        self.start_obb_save(destination, allow_overwrite=True)

    def start_obb_save(self, destination: Path, *, allow_overwrite: bool) -> None:
        if self.obb_session is None:
            return
        if self.obb_save_thread is not None and self.obb_save_thread.is_alive():
            return
        while True:
            try:
                self.obb_save_queue.get_nowait()
            except queue.Empty:
                break
        session = self.obb_session
        self.obb_progress.start(12)
        self.status.configure(text="Starting verified OBB rebuild ...")
        self.refresh_obb_controls()

        def progress(message: str) -> None:
            self.obb_save_queue.put(("progress", message))

        def worker() -> None:
            try:
                report = session.save_obb(
                    destination,
                    allow_overwrite=allow_overwrite,
                    progress=progress,
                )
                self.obb_save_queue.put(("complete", report, session))
            except Exception as error:  # noqa: BLE001
                self.obb_save_queue.put(("error", str(error)))

        self.obb_save_thread = threading.Thread(
            target=worker, name="nba2k20-direct-obb-save", daemon=True
        )
        self.obb_save_thread.start()
        self.refresh_obb_controls()
        self.root.after(150, self.poll_obb_save)

    def poll_obb_save(self) -> None:
        latest = None
        complete = None
        error_text = None
        while True:
            try:
                message = self.obb_save_queue.get_nowait()
            except queue.Empty:
                break
            if message[0] == "progress":
                latest = message[1]
            elif message[0] == "complete":
                complete = (message[1], message[2])
            elif message[0] == "error":
                error_text = message[1]
        if latest:
            self.status.configure(text=latest)
        if complete is not None or error_text is not None:
            self.obb_progress.stop()
            self.obb_save_thread = None
            if error_text is not None:
                self.refresh_obb_controls()
                self.status.configure(text="OBB save failed; source archive was not replaced")
                self.messagebox.showerror("OBB save failed", error_text)
                return
            report, saved_session = complete
            output_path = Path(report["output_obb"]).resolve()
            if not report["overwrote_source"]:
                # Save Copy behaves like Save As: the verified output becomes the
                # active archive and no staged state remains pending.
                cache_dir = saved_session.cache_dir
                for staged in saved_session.staged.values():
                    staged.raw_path.unlink(missing_ok=True)
                saved_session.staged.clear()
                self.obb_session = DirectObbSession(output_path, cache_dir)
            self.obb_rows = self.obb_session.rows() if self.obb_session else []
            self.refresh_obb_controls()
            self.refresh_obb_browser()
            self.refresh_file_tree()
            self.status.configure(text=f"Saved and verified OBB: {output_path}")
            self.messagebox.showinfo(
                "OBB saved",
                f"Rebuilt OBB saved and verified:\n{output_path}\n\n"
                f"Changed entries: {report['changed_entry_count']}\n"
                f"Archive CRC32: {report['archive_crc32']}\n"
                f"Report:\n{report['report']}",
            )
            return
        if self.obb_save_thread is not None and self.obb_save_thread.is_alive():
            self.root.after(180, self.poll_obb_save)

    def save_copy(self) -> None:
        if not self.opened:
            self.messagebox.showinfo("Save IFF copy", "Open an IFF file first.")
            return
        base = re.sub(
            r"\.iff(?:\.decompressed)?$", "", self.opened.path.name, flags=re.IGNORECASE
        )
        initial_name = base + "_edited.iff"
        destination = self.filedialog.asksaveasfilename(
            title="Save edited IFF as a new file",
            defaultextension=".iff",
            initialfile=initial_name,
            filetypes=(("NBA 2K IFF", "*.iff"), ("All files", "*.*")),
        )
        if not destination:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Rebuilding and verifying IFF ...")
        self.root.update_idletasks()
        try:
            report = save_iff(self.opened, Path(destination))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Save failed", str(error))
            self.status.configure(text="Save failed")
            return
        finally:
            self.root.configure(cursor="")
        self.dirty = False
        self.file_label.configure(text=self.opened.path.name)
        self.status.configure(text=f"Saved and verified {destination}")
        self.messagebox.showinfo(
            "IFF saved",
            f"Edited IFF saved and verified:\n{destination}\n\n"
            f"Container mode: {report['mode']}\n"
            "The original IFF was not overwritten.",
        )

    def selected_texture(self) -> TextureRecord | None:
        if not self.opened or not self.tree.selection():
            return None
        return self.opened.textures[int(self.tree.selection()[0])]

    def show_uniform_visual(self) -> None:
        if not self.opened:
            self.messagebox.showinfo("Uniform atlas", "Open a uniform IFF first.")
            return
        for texture in self.opened.textures:
            if texture.format_id == FORMAT_RGBA8888_RAW:
                iid = str(texture.number - 1)
                self.detail_notebook.select(self.texture_tab)
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
                self.on_select()
                return
        self.messagebox.showinfo(
            "Uniform atlas",
            "No high-confidence RGBA8888 atlas was detected in this IFF.",
        )

    def selected_model(self) -> MeshRecord | None:
        if not self.opened or not self.model_tree.selection():
            return None
        return self.opened.meshes[int(self.model_tree.selection()[0])]

    def selected_resource(self) -> ResourceRecord | None:
        if not self.opened or not self.resource_tree.selection():
            return None
        return self.opened.resources[int(self.resource_tree.selection()[0])]

    def auto_fix_selected_etc2(self) -> None:
        texture = self.selected_texture()
        if not self.opened or texture is None:
            self.messagebox.showinfo("Auto Fix ETC2", "Select an ETC2 texture first.")
            return
        if texture.format_id not in (15, 16):
            self.messagebox.showinfo("Auto Fix ETC2", "This feature is only for ETC2 RGB / ETC2 RGBA8 textures.")
            return
        if decode_etc2_auto is None:
            self.messagebox.showerror("Auto Fix ETC2", "The Android ETC2 repair decoder is missing from this build.")
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Analyzing ETC2 block layout ...")
        self.root.update_idletasks()
        try:
            start = texture.payload_offset
            if start is None:
                raise ValueError(texture.error or "texture payload location is unknown")
            payload = bytes(self.opened.data[start:start + texture.payload_size])
            decoded, layout, score = decode_etc2_auto(
                payload, texture.width, texture.height,
                rgba8=texture.format_id == 16, force=True,
            )
            texture.decode_layout = layout
            texture.decode_score = score
            self.on_select()
            self.status.configure(text=f"ETC2 decoder: {layout} | score {score:.2f}")
        except Exception as error:
            self.messagebox.showerror("ETC2 repair failed", str(error))
            self.status.configure(text="ETC2 repair failed")
        finally:
            self.root.configure(cursor="")

    def on_select(self, _event=None) -> None:
        texture = self.selected_texture()
        if not self.opened or texture is None:
            return
        try:
            image = decode_texture(self.opened, texture)
            # On portrait Android screens the preview Label is much narrower
            # than the desktop preview target.  Rendering an 820px-wide image
            # makes Tkinter clip the sides instead of fitting it.  Calculate a
            # target from the actual mobile preview area so the entire texture
            # (including 2048x1024 2:1 banners) is always visible.
            if self.mobile_ui:
                try:
                    self.root.update_idletasks()
                    available_w = max(240, self.preview_label.winfo_width() - 12)
                    available_h = max(120, self.preview_label.winfo_height() - 12)
                    maximum = (available_w, available_h)
                except Exception:
                    maximum = (640, 240)
            else:
                maximum = (820, 590)
            preview = texture_editing_preview(
                image,
                maximum,
                self.texture_preview_mode_var.get(),
                self.texture_preview_sharp_var.get(),
            )
            image.close()
            self.preview_photo = ImageTk.PhotoImage(preview)
            preview.close()
            self.preview_label.configure(
                image=self.preview_photo,
                text=(
                    f"Texture #{texture.number}   {texture.width}x{texture.height}   "
                    f"{FORMAT_NAMES[texture.format_id]}\n"
                    + (f"{texture.label}\n" if texture.label else "")
                    + f"View: {self.texture_preview_mode_var.get()}   "
                    + ("pixel-sharp" if self.texture_preview_sharp_var.get() else "smooth")
                ),
                font="TkDefaultFont",
                anchor="center",
                justify="center",
            )
            self.status.configure(text=f"Previewing {texture_filename(texture)}")
        except Exception as error:  # noqa: BLE001 - display decode problem
            self.preview_photo = None
            self.preview_label.configure(
                image="",
                text=f"Cannot preview this texture:\n\n{error}",
                font="TkDefaultFont",
                anchor="center",
                justify="center",
            )
            self.status.configure(text="Texture preview unavailable")

    def on_model_select(self, _event=None) -> None:
        mesh = self.selected_model()
        if not self.opened or mesh is None:
            return
        try:
            preview = mesh_wireframe_image(self.opened, mesh, (820, 590))
            self.preview_photo = ImageTk.PhotoImage(preview)
            preview.close()
            self.preview_label.configure(
                image=self.preview_photo,
                text="",
                font="TkDefaultFont",
                anchor="center",
                justify="center",
            )
            self.status.configure(
                text=(
                    f"Previewing validated mesh #{mesh.number}: "
                    f"{mesh.vertex_count:,} vertices, {mesh.triangle_count:,} triangles"
                )
            )
        except Exception as error:  # noqa: BLE001
            self.preview_photo = None
            self.preview_label.configure(
                image="",
                text=f"Cannot preview this 3D model:\n\n{error}",
                font="TkDefaultFont",
                anchor="center",
                justify="center",
            )
            self.status.configure(text="3D model preview unavailable")

    def export_selected_model(self) -> None:
        mesh = self.selected_model()
        if not self.opened or mesh is None:
            self.messagebox.showinfo("Export OBJ", "Select a validated 3D model first.")
            return
        destination = self.filedialog.asksaveasfilename(
            title="Export validated 3D model as OBJ",
            initialfile=f"{self.opened.path.stem}_mesh_{mesh.number:03d}.obj",
            defaultextension=".obj",
            filetypes=(("Wavefront OBJ", "*.obj"), ("All files", "*.*")),
        )
        if not destination:
            return
        try:
            export_mesh_obj(self.opened, mesh, Path(destination))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("OBJ export failed", str(error))
            self.status.configure(text="OBJ export failed")
            return
        self.status.configure(text=f"Exported validated 3D model to {destination}")

    def import_selected_model(self) -> None:
        mesh = self.selected_model()
        if not self.opened or mesh is None:
            self.messagebox.showinfo("Import OBJ", "Select a validated 3D model first.")
            return
        if not self.messagebox.askyesno(
            "Import edited OBJ positions?",
            "The OBJ must come from Export Selected OBJ and retain exactly the same "
            "vertex count and vertex order. Only XYZ positions will be imported; "
            "normals, tangents, UVs, skin weights, bone indices, and faces remain "
            "unchanged. Continue?",
        ):
            return
        selected = self.filedialog.askopenfilename(
            title=f"Import edited OBJ for mesh #{mesh.number}",
            filetypes=(("Wavefront OBJ", "*.obj"), ("All files", "*.*")),
        )
        if not selected:
            return
        try:
            change = import_mesh_obj(self.opened, mesh, Path(selected))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("OBJ import failed", str(error))
            self.status.configure(text="OBJ import failed")
            return
        self.changes.append(change)
        self.dirty = True
        self.file_label.configure(text=self.opened.path.name + " *")
        self.on_model_select()
        self.status.configure(
            text=(
                f"Imported {mesh.vertex_count:,} OBJ vertex positions; use Save IFF "
                "or Save IFF Copy next"
            )
        )

    def export_every_model(self) -> None:
        if not self.opened or not self.opened.meshes:
            self.messagebox.showinfo(
                "Export all OBJ", "This IFF has no currently validated 3D model layout."
            )
            return
        selected = self.filedialog.askdirectory(
            title="Choose folder for exported OBJ models"
        )
        if not selected:
            return
        destination = Path(selected)
        try:
            for mesh in self.opened.meshes:
                export_mesh_obj(
                    self.opened,
                    mesh,
                    destination
                    / f"{self.opened.path.stem}_mesh_{mesh.number:03d}.obj",
                )
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("OBJ export failed", str(error))
            self.status.configure(text="OBJ export failed")
            return
        self.messagebox.showinfo(
            "OBJ models exported",
            f"Exported {len(self.opened.meshes):,} validated OBJ model(s) to:\n{destination}",
        )
        self.status.configure(text=f"Exported {len(self.opened.meshes):,} OBJ model(s)")

    def on_resource_select(self, _event=None) -> None:
        resource = self.selected_resource()
        if not self.opened or resource is None:
            return
        if resource.kind == "Texture payload" and resource.texture_number is not None:
            try:
                texture = self.opened.textures[resource.texture_number - 1]
                image = decode_texture(self.opened, texture)
                preview = checker_preview(image, (820, 590))
                image.close()
                self.preview_photo = ImageTk.PhotoImage(preview)
                preview.close()
                self.preview_label.configure(
                    image=self.preview_photo,
                    text=(
                        f"{resource.name}   0x{resource.offset:X}   "
                        f"{resource.size:,} bytes\n"
                    ),
                    font="TkDefaultFont",
                    anchor="center",
                    justify="center",
                )
                self.status.configure(text=f"Previewing {resource.name}")
                return
            except Exception:  # noqa: BLE001 - raw preview remains available
                pass
        if resource.extension.lower() in (".png", ".jpg", ".jpeg", ".webp"):
            try:
                raw = resource_bytes(self.opened, resource)
                with Image.open(io.BytesIO(raw)) as embedded:
                    image = embedded.convert("RGBA")
                preview = checker_preview(image, (820, 590))
                image.close()
                self.preview_photo = ImageTk.PhotoImage(preview)
                preview.close()
                self.preview_label.configure(
                    image=self.preview_photo,
                    text=(
                        f"{resource.name}   0x{resource.offset:X}   "
                        f"{resource.size:,} bytes\n"
                    ),
                    font="TkDefaultFont",
                    anchor="center",
                    justify="center",
                )
                self.status.configure(text=f"Previewing {resource.name}")
                return
            except Exception:  # noqa: BLE001 - fall back to exact hex preview
                pass
        self.preview_photo = None
        self.preview_label.configure(
            image="",
            text=resource_preview_text(self.opened, resource),
            font=("Consolas", 11 if self.mobile_ui else 9),
            anchor="nw",
            justify="left",
        )
        self.status.configure(
            text=(
                f"Resource #{resource.number}: {resource.kind}, "
                f"0x{resource.offset:X}-0x{resource.end:X}"
            )
        )

    def export_selected_resource(self) -> None:
        resource = self.selected_resource()
        if not self.opened or resource is None:
            self.messagebox.showinfo("Export raw resource", "Select an All Resources row first.")
            return
        destination = self.filedialog.asksaveasfilename(
            title="Export exact resource bytes",
            initialfile=resource_filename(resource),
            defaultextension=resource.extension or ".bin",
            filetypes=(("All files", "*.*"),),
        )
        if not destination:
            return
        try:
            Path(destination).write_bytes(resource_bytes(self.opened, resource))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Raw export failed", str(error))
            self.status.configure(text="Raw resource export failed")
            return
        self.status.configure(text=f"Exported {destination}")

    def import_selected_resource(self) -> None:
        resource = self.selected_resource()
        if not self.opened or resource is None:
            self.messagebox.showinfo("Import raw resource", "Select an All Resources row first.")
            return
        if resource.container and not self.messagebox.askyesno(
            "Replace complete IFF block?",
            "This row is a complete container block. Replacing it changes all resources "
            "inside that block. Continue only if your replacement has the exact same layout.",
        ):
            return
        selected = self.filedialog.askopenfilename(
            title=f"Choose exact {resource.size:,}-byte replacement for {resource.name}",
            filetypes=(("All files", "*.*"),),
        )
        if not selected:
            return
        try:
            change = import_raw_resource(self.opened, resource, Path(selected))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Raw import failed", str(error))
            self.status.configure(text="Raw resource import failed")
            return
        self.changes.append(change)
        self.dirty = True
        self.file_label.configure(text=self.opened.path.name + " *")
        self.on_resource_select()
        self.status.configure(
            text=(
                f"Imported exact-size resource #{resource.number}; "
                "use Save IFF or Save IFF Copy next"
            )
        )

    def open_selected_resource_external(self) -> None:
        resource = self.selected_resource()
        if not self.opened or resource is None:
            self.messagebox.showinfo("Open resource", "Select an All Resources row first.")
            return
        supported = {
            ".ogg", ".wav", ".avi", ".webp", ".png", ".jpg",
            ".xml", ".glsl", ".txt",
        }
        if resource.extension.lower() not in supported:
            self.messagebox.showinfo(
                "No associated preview format",
                "This resource has no standard standalone media format yet. "
                "Use Export Selected Raw, or use its specialized texture/model parser when available.",
            )
            return
        destination = Path(self.external_temp.name) / resource_filename(resource)
        try:
            destination.write_bytes(resource_bytes(self.opened, resource))
            os.startfile(destination)  # type: ignore[attr-defined]
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Cannot open resource", str(error))
            self.status.configure(text="External resource preview failed")
            return
        self.status.configure(text=f"Opened {resource.name} with the Windows default app")

    def export_every_resource(self) -> None:
        if not self.opened:
            self.messagebox.showinfo("Export all resources", "Open an IFF file first.")
            return
        selected = self.filedialog.askdirectory(
            title="Choose folder for every IFF resource and raw region"
        )
        if not selected:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Exporting all identified and unclassified resources ...")
        self.root.update_idletasks()
        try:
            count, byte_count = export_all_resources(self.opened, Path(selected))
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Resource export failed", str(error))
            self.status.configure(text="Resource export failed")
            return
        finally:
            self.root.configure(cursor="")
        coverage = "complete" if byte_count == len(self.opened.data) else "requires review"
        self.messagebox.showinfo(
            "All resources exported",
            f"Exported {count:,} resource/raw-region file(s) to:\n{selected}\n\n"
            f"Byte coverage: {byte_count:,}/{len(self.opened.data):,} ({coverage}).\n"
            "See IFF_ALL_RESOURCES_MANIFEST.json for types, offsets, and notes.",
        )
        self.status.configure(text=f"Exported {count:,} resource row(s); byte coverage {coverage}")

    def export_selected(self) -> None:
        texture = self.selected_texture()
        if not self.opened or texture is None:
            self.messagebox.showinfo("Export PNG", "Select a texture first.")
            return
        destination = self.filedialog.asksaveasfilename(
            title="Export texture as PNG",
            defaultextension=".png",
            initialfile=texture_filename(texture),
            filetypes=(("PNG image", "*.png"),),
        )
        if not destination:
            return
        try:
            image = decode_texture(self.opened, texture)
            image.save(destination)
            image.close()
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("Export failed", str(error))
            return
        self.status.configure(text=f"Exported {destination}")

    def export_selected_jpeg(self) -> None:
        texture = self.selected_texture()
        if not self.opened or texture is None:
            self.messagebox.showinfo("Export JPEG", "Select a texture first.")
            return
        destination = self.filedialog.asksaveasfilename(
            title="Export texture as JPEG",
            defaultextension=".jpg",
            initialfile=Path(texture_filename(texture)).with_suffix(".jpg").name,
            filetypes=(("JPEG image", "*.jpg"), ("JPEG image", "*.jpeg")),
        )
        if not destination:
            return
        try:
            image = decode_texture(self.opened, texture)
            # JPEG has no alpha channel. Composite transparent ETC2/RGBA pixels
            # onto black rather than letting Pillow discard the alpha implicitly.
            if image.mode == "RGBA":
                background = Image.new("RGB", image.size, (0, 0, 0))
                background.paste(image, mask=image.getchannel("A"))
                background.save(destination, "JPEG", quality=95, optimize=True)
                background.close()
            else:
                image.convert("RGB").save(destination, "JPEG", quality=95, optimize=True)
            image.close()
        except Exception as error:  # noqa: BLE001
            self.messagebox.showerror("JPEG export failed", str(error))
            return
        self.status.configure(text=f"Exported {destination}")

    def export_everything(self) -> None:
        if not self.opened:
            self.messagebox.showinfo("Export all", "Open an IFF file first.")
            return
        selected = self.filedialog.askdirectory(title="Choose folder for exported PNG files")
        if not selected:
            return
        self.root.configure(cursor="watch")
        self.status.configure(text="Exporting textures ...")
        self.root.update_idletasks()
        try:
            count, errors = export_all(self.opened, Path(selected))
        finally:
            self.root.configure(cursor="")
        message = f"Exported {count} PNG texture(s) to:\n{selected}"
        if errors:
            message += f"\n\n{len(errors)} texture(s) could not be exported; see IFF_TEXTURE_MANIFEST.json."
        self.messagebox.showinfo("Export complete", message)
        self.status.configure(text=f"Exported {count} texture(s)")

    def run(self) -> None:
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.mainloop()

    def on_close(self) -> None:
        if self.obb_save_thread is not None and self.obb_save_thread.is_alive():
            self.messagebox.showinfo(
                "OBB save is running",
                "Wait for the verified OBB rebuild to finish before closing the manager.",
            )
            return
        if self.catalog_thread is not None and self.catalog_thread.is_alive():
            if not self.messagebox.askyesno(
                "Catalog is running",
                "Stop the folder catalog safely and close the viewer?",
            ):
                return
            self.catalog_cancel.set()
        if self.dirty and not self.messagebox.askyesno(
            "Unsaved IFF changes", "Exit and discard the imported texture/raw changes?"
        ):
            return
        if (
            self.obb_session is not None
            and self.obb_session.staged
            and not self.messagebox.askyesno(
                "Unsaved OBB changes",
                f"Discard {len(self.obb_session.staged)} IFF entry edit(s) staged for "
                "the OBB but not saved to an archive?",
            )
        ):
            return
        self.external_temp.cleanup()
        self.root.destroy()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, help="IFF file to open")
    parser.add_argument(
        "--list",
        action="store_true",
        help="print detected texture and all-resource metadata as JSON",
    )
    parser.add_argument("--export-all", type=Path, metavar="FOLDER", help="export every supported texture without opening the GUI")
    parser.add_argument(
        "--export-resources",
        type=Path,
        metavar="FOLDER",
        help="export every identified resource and unclassified byte region",
    )
    parser.add_argument(
        "--replace",
        action="append",
        nargs=2,
        metavar=("TEXTURE_NUMBER", "PNG"),
        help="replace one texture; may be specified more than once",
    )
    parser.add_argument(
        "--replace-folder",
        type=Path,
        metavar="FOLDER",
        help="replace every PNG matching its Export All PNG filename",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="new IFF path used with --replace or --replace-folder",
    )
    parser.add_argument(
        "--scan-folder",
        type=Path,
        metavar="FOLDER",
        help="list every IFF in a folder as JSON without opening the GUI",
    )
    parser.add_argument(
        "--catalog-folder",
        type=Path,
        metavar="FOLDER",
        help="build/resume the searchable all-IFF contents catalog without the GUI",
    )
    args = parser.parse_args()

    if args.catalog_folder:
        def report(index, total, path, outcome, error_text) -> None:
            if outcome == "error" or index == total or index % 100 == 0:
                suffix = f": {error_text}" if error_text else ""
                print(f"[{index}/{total}] {path.name} {outcome}{suffix}", flush=True)

        result = build_folder_catalog(args.catalog_folder, progress=report)
        print(json.dumps(result, indent=2))
        return 0

    if args.scan_folder:
        folder = args.scan_folder.resolve()
        files = find_iff_files(folder)
        print(
            json.dumps(
                {
                    "folder": str(folder),
                    "count": len(files),
                    "files": [str(path.relative_to(folder)) for path in files],
                },
                indent=2,
            )
        )
        return 0

    if (
        args.list
        or args.export_all
        or args.export_resources
        or args.replace
        or args.replace_folder
    ):
        if args.input is None:
            parser.error("an input IFF is required for command-line operations")
        opened = open_iff(args.input)
        changes = []
        batch_report = None
        if args.replace or args.replace_folder:
            if args.output is None:
                parser.error("--output is required with --replace or --replace-folder")
        if args.replace:
            for number_text, png_text in args.replace:
                try:
                    number = int(number_text)
                except ValueError as error:
                    raise ValueError(f"invalid texture number: {number_text}") from error
                if number < 1 or number > len(opened.textures):
                    raise ValueError(
                        f"texture number must be 1-{len(opened.textures)}, got {number}"
                    )
                changes.append(import_png(opened, opened.textures[number - 1], Path(png_text)))
        if args.replace_folder:
            batch_report = import_all_exported_pngs(opened, args.replace_folder)
            changes.extend(batch_report["changes"])
        if args.replace or args.replace_folder:
            save_report = save_iff(opened, args.output)
            print(
                json.dumps(
                    {
                        "changes": changes,
                        "batch": batch_report,
                        "save": save_report,
                    },
                    indent=2,
                )
            )
        if args.list:
            print(json.dumps(opened.summary(), indent=2))
        if args.export_all:
            count, errors = export_all(opened, args.export_all)
            print(f"exported {count} texture(s) to {args.export_all}")
            for error in errors:
                print(f"warning: {error}", file=sys.stderr)
        if args.export_resources:
            count, byte_count = export_all_resources(opened, args.export_resources)
            print(
                f"exported {count} resource/raw-region file(s), "
                f"covering {byte_count}/{len(opened.data)} decompressed bytes, "
                f"to {args.export_resources}"
            )
        return 0

    Viewer(args.input).run()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, zlib.error) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)

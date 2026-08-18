#!/usr/bin/env python3
"""Rebuild an NBA 2K20 OBB from a folder produced by obb_decrypt.py.

Only entries whose extracted file was actually edited are rebuilt; every
other entry is copied through byte-for-byte unchanged. For "zlib"-mode
entries, the edited file's byte length must exactly match the original
decompressed length recorded in the manifest: the container's block layout
is fixed at that size, so content can be re-encoded but not grown or
shrunk. For "raw"-mode entries any length is accepted.

Usage:
    python obb_encrypt.py <source_obb> <edited_dir> <output_obb>
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import shutil
import struct
import sys
import zlib
from pathlib import Path

TOOLS_DIR = Path(__file__).parent
sys.path.insert(0, str(TOOLS_DIR))
from nba2k20_obb import (  # noqa: E402
    ALIGNMENT,
    RECORD,
    TABLE_OFFSET,
    TYPE_COMPRESSED,
    TYPE_ZLIB,
    Obb,
)

BINFILE_CHECKSUM_OFFSET = 0x38
TOTAL_BLOCKS_OFFSET = 0x28
TOOL_FORMAT_VERSION = 2
COPY_CHUNK = 16 * 1024 * 1024


@dataclasses.dataclass
class Block:
    position: int
    unpacked_size: int
    stored_size: int
    flags: int
    original_sha256: bytes


@dataclasses.dataclass
class BuiltEntry:
    name: str
    index: int
    offset: int
    slot_size: int
    data: bytes
    expected_sha256: str
    expected_size: int
    is_zlib: bool
    mode: str


def sha256_bytes(data: bytes | bytearray | memoryview) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(COPY_CHUNK):
            digest.update(chunk)
    return digest.hexdigest().upper()


def read_exact_sha256(path: Path, offset: int, size: int) -> str:
    digest = hashlib.sha256()
    remaining = size
    with path.open("rb") as stream:
        stream.seek(offset)
        while remaining:
            chunk = stream.read(min(COPY_CHUNK, remaining))
            if not chunk:
                raise EOFError(
                    f"{path.name}: expected {size} bytes at offset {offset}, "
                    f"stopped with {remaining} bytes remaining"
                )
            digest.update(chunk)
            remaining -= len(chunk)
    return digest.hexdigest().upper()


def require_workspace_file(workspace: Path, relative_name: str) -> Path:
    candidate = (workspace / relative_name).resolve()
    try:
        candidate.relative_to(workspace)
    except ValueError as error:
        raise ValueError(f"manifest file escapes the workspace: {relative_name}") from error
    if not candidate.is_file():
        raise ValueError(f"workspace entry is missing: {candidate}")
    return candidate


def validate_manifest_source(manifest: dict, obb: Obb, source_sha256: str) -> None:
    if manifest.get("tool_format_version") != TOOL_FORMAT_VERSION:
        raise ValueError(
            "unsupported or old extraction manifest; extract the OBB again with "
            "this tool pack before rebuilding"
        )
    if manifest.get("source_obb_size") != obb.path.stat().st_size:
        raise ValueError("source OBB size does not match the extraction manifest")
    if str(manifest.get("source_obb_sha256", "")).upper() != source_sha256:
        raise ValueError(
            "source OBB SHA-256 does not match the extraction manifest; use the "
            "same untouched OBB that created this workspace"
        )
    if manifest.get("entry_count") != len(obb.entries):
        raise ValueError("source OBB entry count does not match the manifest")
    records = manifest.get("entries")
    if not isinstance(records, list) or len(records) != len(obb.entries):
        raise ValueError("manifest entry list is incomplete")

    seen: set[int] = set()
    entries_by_index = {entry.index: entry for entry in obb.entries}
    for record in records:
        index = record.get("index")
        if not isinstance(index, int) or index not in entries_by_index:
            raise ValueError(f"manifest has an invalid entry index: {index!r}")
        if index in seen:
            raise ValueError(f"manifest repeats entry index {index}")
        seen.add(index)
        entry = entries_by_index[index]
        expected = {
            "hash": f"{entry.name_hash:08x}",
            "block": entry.block,
            "length": entry.length,
            "reserved": entry.reserved,
            "stored_size": obb.stored_size(entry),
        }
        for field, value in expected.items():
            actual = record.get(field)
            if field == "hash" and isinstance(actual, str):
                actual = actual.lower()
            if actual != value:
                raise ValueError(
                    f"manifest/source mismatch at entry {index}, field {field}: "
                    f"manifest={actual!r}, source={value!r}"
                )


def compress_zlib_max(data: bytes | bytearray | memoryview) -> bytes:
    """Try compatible zlib workspace/strategy variants and keep the smallest."""
    candidates = [zlib.compress(data, level=9)]
    for memory_level in (8, 9):
        for strategy in (zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED):
            compressor = zlib.compressobj(
                level=9,
                method=zlib.DEFLATED,
                wbits=15,
                memLevel=memory_level,
                strategy=strategy,
            )
            candidates.append(compressor.compress(data) + compressor.flush())
    return min(candidates, key=len)


def align_up(value: int, alignment: int) -> int:
    return (value + alignment - 1) // alignment * alignment


def compute_archive_crc32(path: Path) -> int:
    """Reproduce VCBinFileDevice_Platform_VerifyDevice's archive checksum."""
    obb = Obb(path)
    checksum = 0
    with path.open("rb") as stream:
        for entry in sorted(obb.entries, key=lambda item: item.block):
            remaining = entry.length
            if not remaining:
                continue
            stream.seek(entry.offset)
            while remaining:
                chunk = stream.read(min(8 * 1024 * 1024, remaining))
                if not chunk:
                    raise EOFError(f"entry {entry.index} ended during CRC calculation")
                checksum = zlib.crc32(chunk, checksum)
                remaining -= len(chunk)
    return checksum


def update_archive_crc32(path: Path) -> int:
    checksum = compute_archive_crc32(path)
    with path.open("r+b") as stream:
        stream.seek(BINFILE_CHECKSUM_OFFSET)
        stream.write(struct.pack("<I", checksum))
    return checksum


def parse_entry(raw: bytes, exact_length: int):
    entry_type = raw[:4]
    if entry_type == TYPE_COMPRESSED:
        first_offset = struct.unpack_from("<I", raw, 4)[0]
        compressed_wrapper = True
    elif entry_type == TYPE_ZLIB:
        first_offset = 0
        compressed_wrapper = False
    else:
        raise ValueError(f"unsupported entry wrapper {entry_type.hex()}")

    position = first_offset
    blocks: list[Block] = []
    unpacked = bytearray()
    while position + 16 <= exact_length and raw[position : position + 4] == TYPE_ZLIB:
        unpacked_size, stored_size, flags = struct.unpack_from(">III", raw, position + 4)
        if stored_size < 16 or position + stored_size > exact_length:
            raise ValueError("invalid ZLIB block size")
        chunk = zlib.decompress(raw[position + 16 : position + stored_size])
        if len(chunk) != unpacked_size:
            raise ValueError("ZLIB block decompressed to the wrong length")
        blocks.append(
            Block(position, unpacked_size, stored_size, flags, hashlib.sha256(chunk).digest())
        )
        unpacked.extend(chunk)
        position += stored_size
    if not blocks:
        raise ValueError("entry contains no ZLIB blocks")
    return unpacked, blocks, first_offset, compressed_wrapper


def rebuild_entry(raw, original_exact_length, modified, blocks, first_offset, compressed_wrapper):
    cursor = 0
    prepared = []
    preserve_possible = True
    changed_blocks = 0
    for block in blocks:
        view = memoryview(modified)[cursor : cursor + block.unpacked_size]
        changed = hashlib.sha256(view).digest() != block.original_sha256
        packed = compress_zlib_max(view) if changed else None
        if changed:
            changed_blocks += 1
            if 16 + len(packed) > block.stored_size:
                preserve_possible = False
        prepared.append((block, packed, changed))
        cursor += block.unpacked_size
    if cursor != len(modified):
        raise ValueError(
            f"edited content is {len(modified)} bytes but the original entry's "
            f"ZLIB blocks total {cursor} bytes -- zlib entries cannot be resized"
        )

    if preserve_possible:
        pieces = [raw[:first_offset]]
        for block, packed, changed in prepared:
            if not changed:
                pieces.append(raw[block.position : block.position + block.stored_size])
                continue
            compact_size = 16 + len(packed)
            pieces.append(
                TYPE_ZLIB
                + struct.pack(">III", block.unpacked_size, block.stored_size, block.flags)
                + packed
                + b"\0" * (block.stored_size - compact_size)
            )
        end = blocks[-1].position + blocks[-1].stored_size
        pieces.append(raw[end:original_exact_length])
        rebuilt = b"".join(pieces)
        if len(rebuilt) != original_exact_length:
            raise ValueError("layout-preserved rebuild changed the entry length")
        return rebuilt, "preserved", changed_blocks

    compact_blocks = []
    for block, packed, changed in prepared:
        if not changed:
            compact_blocks.append(raw[block.position : block.position + block.stored_size])
            continue
        compact_blocks.append(
            TYPE_ZLIB
            + struct.pack(">III", block.unpacked_size, 16 + len(packed), block.flags)
            + packed
        )

    prefix = bytearray(raw[:first_offset])
    if compressed_wrapper:
        position = first_offset
        for index, block_bytes in enumerate(compact_blocks):
            descriptor = 0x2C + index * 0x38
            if descriptor + 0x30 > len(prefix):
                raise ValueError("compressed wrapper has no matching resource descriptor")
            struct.pack_into("<I", prefix, descriptor + 0x24, position)
            struct.pack_into("<I", prefix, descriptor + 0x2C, len(block_bytes))
            position += len(block_bytes)
        rebuilt_array = bytearray(prefix + b"".join(compact_blocks))
        struct.pack_into(">I", rebuilt_array, 8, len(rebuilt_array))
        rebuilt = bytes(rebuilt_array)
    else:
        rebuilt = b"".join(compact_blocks)
    return rebuilt, "compact", changed_blocks


def apply_entries(source: Path, output: Path, entries: list[BuiltEntry]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as src, output.open("wb") as dst:
        shutil.copyfileobj(src, dst, length=16 * 1024 * 1024)

    append_position = output.stat().st_size
    if append_position % ALIGNMENT:
        raise ValueError("source OBB does not end on an alignment boundary")
    with output.open("r+b") as stream:
        for built in entries:
            if built.mode != "append":
                stream.seek(built.offset)
                stream.write(built.data)
                stream.write(b"\0" * (built.slot_size - len(built.data)))
                block = built.offset // ALIGNMENT
            else:
                block = append_position // ALIGNMENT
                stream.seek(append_position)
                stream.write(built.data)
                padded = align_up(len(built.data), ALIGNMENT)
                stream.write(b"\0" * (padded - len(built.data)))
                append_position += padded
            stream.seek(TABLE_OFFSET + built.index * RECORD.size)
            stream.write(struct.pack("<I", len(built.data)))
            stream.seek(TABLE_OFFSET + built.index * RECORD.size + 12)
            stream.write(struct.pack("<I", block))
        stream.seek(TOTAL_BLOCKS_OFFSET)
        stream.write(struct.pack("<Q", append_position // ALIGNMENT))


def decompressed_sha256(obb: Obb, entry) -> tuple[str, int]:
    digest = hashlib.sha256()
    total = 0
    with obb.path.open("rb") as stream:
        for chunk in obb.decompressed_chunks(stream, entry):
            digest.update(chunk)
            total += len(chunk)
    return digest.hexdigest().upper(), total


def verify_output(path: Path, entries: list[BuiltEntry], archive_crc32: int) -> None:
    obb = Obb(path)
    entries_by_index = {entry.index: entry for entry in obb.entries}
    for built in entries:
        entry = entries_by_index[built.index]
        if built.is_zlib:
            digest, total = decompressed_sha256(obb, entry)
        else:
            with obb.path.open("rb") as stream:
                stream.seek(entry.offset)
                digest = sha256_bytes(stream.read(built.expected_size))
                total = built.expected_size
        if (digest, total) != (built.expected_sha256, built.expected_size):
            raise ValueError(f"verification failed for {built.name}")
    with path.open("rb") as stream:
        stream.seek(BINFILE_CHECKSUM_OFFSET)
        stored_crc32 = struct.unpack("<I", stream.read(4))[0]
    if stored_crc32 != archive_crc32 or compute_archive_crc32(path) != archive_crc32:
        raise ValueError("archive CRC verification failed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_obb", type=Path)
    parser.add_argument("edited_dir", type=Path)
    parser.add_argument("output_obb", type=Path)
    parser.add_argument(
        "--force",
        action="store_true",
        help="allow overwriting an existing output OBB (the source is never overwritten)",
    )
    args = parser.parse_args()

    source_path = args.source_obb.resolve()
    workspace = args.edited_dir.resolve()
    output_path = args.output_obb.resolve()
    if not source_path.is_file():
        raise ValueError(f"source OBB was not found: {source_path}")
    if not workspace.is_dir():
        raise ValueError(f"edited workspace was not found: {workspace}")
    if output_path == source_path:
        raise ValueError("output OBB must be a new file; the source is never overwritten")
    if output_path.exists() and not args.force:
        raise ValueError(
            f"output already exists: {output_path} (choose a new name or add --force)"
        )

    manifest_path = workspace / "manifest.json"
    if not manifest_path.is_file():
        raise ValueError(f"extraction manifest was not found: {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    obb = Obb(source_path)
    print("hashing and validating the untouched source OBB", flush=True)
    source_sha256 = sha256_path(source_path)
    validate_manifest_source(manifest, obb, source_sha256)
    entries_by_index = {entry.index: entry for entry in obb.entries}

    built_entries: list[BuiltEntry] = []
    unchanged = 0
    with obb.path.open("rb") as stream:
        for record in manifest["entries"]:
            entry = entries_by_index[record["index"]]
            edited_path = require_workspace_file(workspace, record["file"])
            edited_size = edited_path.stat().st_size
            edited_digest = sha256_path(edited_path)
            label = record["name"] or record["hash"]
            original_digest = str(record["extracted_sha256"]).upper()

            if edited_digest == original_digest and edited_size == record["extracted_size"]:
                unchanged += 1
                continue

            if record["mode"] == "zlib":
                current_digest, current_size = decompressed_sha256(obb, entry)
                if (current_digest, current_size) != (
                    original_digest,
                    record["decompressed_size"],
                ):
                    raise ValueError(
                        f"{label}: source entry no longer matches the extraction manifest"
                    )
                if edited_size != record["decompressed_size"]:
                    raise ValueError(
                        f"{label}: edited file is {edited_size} bytes, original "
                        f"decompressed size is {record['decompressed_size']} bytes -- "
                        "zlib entries cannot change size, only content"
                    )
                edited_bytes = edited_path.read_bytes()
                stream.seek(entry.offset)
                raw = stream.read(obb.stored_size(entry))
                _, blocks, first_offset, compressed_wrapper = parse_entry(raw, entry.length)
                rebuilt, mode, changed_blocks = rebuild_entry(
                    raw, entry.length, bytearray(edited_bytes), blocks, first_offset, compressed_wrapper
                )
                if len(rebuilt) > obb.stored_size(entry):
                    mode = "append"
                built_entries.append(
                    BuiltEntry(
                        label, entry.index, entry.offset, obb.stored_size(entry),
                        rebuilt, edited_digest, edited_size, True, mode,
                    )
                )
                print(f"rebuilt {label}: {changed_blocks} block(s) recompressed, mode={mode}")
            elif record["mode"] == "raw":
                current_digest = read_exact_sha256(obb.path, entry.offset, entry.length)
                if current_digest != original_digest:
                    raise ValueError(
                        f"{label}: source raw entry no longer matches the extraction manifest"
                    )
                edited_bytes = edited_path.read_bytes()
                stream.seek(entry.offset)
                mode = "preserved" if len(edited_bytes) <= obb.stored_size(entry) else "append"
                built_entries.append(
                    BuiltEntry(
                        label, entry.index, entry.offset, obb.stored_size(entry),
                        edited_bytes, sha256_bytes(edited_bytes), len(edited_bytes), False, mode,
                    )
                )
                print(f"replaced raw entry {label} ({len(edited_bytes)} bytes, mode={mode})")
            else:
                raise ValueError(f"{label}: unsupported manifest mode {record['mode']!r}")

    if not built_entries:
        print("no entries were changed; nothing to rebuild")
        return 0

    apply_entries(source_path, output_path, built_entries)
    archive_crc32 = update_archive_crc32(output_path)
    verify_output(output_path, built_entries, archive_crc32)
    print("hashing rebuilt OBB", flush=True)
    output_sha256 = sha256_path(output_path)

    report = {
        "tool_format_version": TOOL_FORMAT_VERSION,
        "source_obb": str(source_path),
        "source_obb_sha256": source_sha256,
        "workspace": str(workspace),
        "output_obb": str(output_path),
        "output_obb_size": output_path.stat().st_size,
        "output_obb_sha256": output_sha256,
        "archive_crc32": f"0x{archive_crc32:08X}",
        "changed_entry_count": len(built_entries),
        "unchanged_entry_count": unchanged,
        "changed_entries": [
            {
                "index": built.index,
                "name": built.name,
                "mode": built.mode,
                "edited_size": built.expected_size,
                "edited_sha256": built.expected_sha256,
            }
            for built in built_entries
        ],
        "verification": "PASS",
    }
    report_path = output_path.with_suffix(output_path.suffix + ".build_report.json")
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(
        f"wrote {output_path} ({len(built_entries)} entries rebuilt, "
        f"{unchanged} unchanged, archive_crc32=0x{archive_crc32:08X})"
    )
    print(f"output_sha256={output_sha256}")
    print(f"report={report_path}")
    print("verification: PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (EOFError, OSError, ValueError, KeyError, zlib.error) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)

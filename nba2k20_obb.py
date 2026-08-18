#!/usr/bin/env python3
"""Inspect and extract NBA 2K20 Android OBB entries.

The game uses a hash-indexed 2K container rather than ZIP/JOBB. This tool is
deliberately read-only: it never modifies an OBB in place.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import json
import re
import struct
import sys
import zlib
from pathlib import Path
from typing import BinaryIO, Iterator


MAGIC = b"\xbf\xb3\x00\xaa"
ALIGNMENT = 2048
# The fixed 0x28-byte header is followed by one 0xd0-byte BINFILE entry.
# TOC records therefore begin at 0xf8. Each record is:
#   uint32 stored_size, uint32 binfile_index, uint32 name_hash, uint32 block
TABLE_OFFSET = 0xF8
RECORD = struct.Struct("<IIII")

TYPE_COMPRESSED = b"\x94\xef\x3b\xff"
TYPE_ZLIB = b"ZLIB"
TYPE_CDF = b"\x30\x50\x98\xf0"
TYPE_DRAM = b"\xdf\x85\xc5\xce"
TYPE_FILELIST = b"\x07\x12\x79\xe4"

TYPE_NAMES = {
    TYPE_COMPRESSED: "compressed",
    TYPE_ZLIB: "zlib-image",
    TYPE_CDF: "cdf",
    TYPE_DRAM: "dram",
    TYPE_FILELIST: "filelist",
    b"OggS": "ogg",
}


@dataclasses.dataclass(frozen=True)
class Entry:
    index: int
    name_hash: int
    block: int
    length: int
    reserved: int

    @property
    def offset(self) -> int:
        return self.block * ALIGNMENT


class Obb:
    def __init__(self, path: Path):
        self.path = path
        self.entries: list[Entry] = []
        with path.open("rb") as stream:
            if stream.read(4) != MAGIC:
                raise ValueError(f"{path} does not have the NBA 2K OBB magic")
            if _read_u32le(stream, 4) != ALIGNMENT:
                raise ValueError(f"{path} does not use {ALIGNMENT}-byte blocks")
            archive_count = _read_u64le(stream, 8)
            if archive_count != 1:
                raise ValueError(f"unsupported embedded archive count: {archive_count}")
            count = _read_u64le(stream, 0x18)
            stream.seek(TABLE_OFFSET)
            for index in range(count):
                length, reserved, name_hash, block = RECORD.unpack(
                    _read_exact(stream, RECORD.size)
                )
                self.entries.append(Entry(index, name_hash, block, length, reserved))

        archive_size = path.stat().st_size
        for entry in self.entries:
            if entry.offset >= archive_size:
                raise ValueError(
                    f"entry {entry.index} starts beyond {path.name}: "
                    f"offset={entry.offset}"
                )

        offsets = sorted({entry.offset for entry in self.entries})
        self._next_offsets = {
            offset: offsets[position + 1] if position + 1 < len(offsets) else archive_size
            for position, offset in enumerate(offsets)
        }

    def stored_size(self, entry: Entry) -> int:
        """Return the physical span assigned to an entry, including alignment padding."""
        return self._next_offsets[entry.offset] - entry.offset

    def type_bytes(self, stream: BinaryIO, entry: Entry) -> bytes:
        stream.seek(entry.offset)
        return _read_exact(stream, 4)

    def decompressed_chunks(
        self, stream: BinaryIO, entry: Entry
    ) -> Iterator[bytes]:
        stream.seek(entry.offset)
        entry_type = _read_exact(stream, 4)

        if entry_type == TYPE_COMPRESSED:
            relative_offset = struct.unpack("<I", _read_exact(stream, 4))[0]
            if relative_offset < 8 or relative_offset >= self.stored_size(entry):
                raise ValueError(
                    f"entry {entry.index} has invalid payload offset {relative_offset}"
                )
            position = entry.offset + relative_offset
        elif entry_type == TYPE_ZLIB:
            position = entry.offset
        else:
            raise ValueError(
                f"entry {entry.index} is not ZLIB-wrapped ({entry_type.hex()})"
            )

        end = entry.offset + self.stored_size(entry)
        block_number = 0
        while position + 16 <= end:
            stream.seek(position)
            if stream.read(4) != TYPE_ZLIB:
                break
            unpacked_size, stored_size, flags = struct.unpack(
                ">III", _read_exact(stream, 12)
            )
            packed_size = stored_size - 16
            if packed_size <= 0 or position + stored_size > end:
                raise ValueError(
                    f"entry {entry.index} block {block_number} has invalid "
                    f"stored size {stored_size}"
                )
            packed = _read_exact(stream, packed_size)
            unpacked = zlib.decompress(packed)
            if len(unpacked) != unpacked_size:
                raise ValueError(
                    f"entry {entry.index} block {block_number}: expected "
                    f"{unpacked_size} bytes, got {len(unpacked)}"
                )
            yield unpacked
            position += stored_size
            block_number += 1

        if block_number == 0:
            raise ValueError(f"entry {entry.index} contains no ZLIB blocks")

    def decompressed_prefix(
        self, stream: BinaryIO, entry: Entry, limit: int
    ) -> bytes:
        output = bytearray()
        for chunk in self.decompressed_chunks(stream, entry):
            output.extend(chunk[: max(0, limit - len(output))])
            if len(output) >= limit:
                break
        return bytes(output)

    def extract(self, entry: Entry, destination: Path, decompressed: bool) -> int:
        destination.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("rb") as source, destination.open("wb") as output:
            if decompressed:
                written = 0
                for chunk in self.decompressed_chunks(source, entry):
                    output.write(chunk)
                    written += len(chunk)
                return written

            source.seek(entry.offset)
            remaining = self.stored_size(entry)
            written = 0
            while remaining:
                chunk = source.read(min(1024 * 1024, remaining))
                if not chunk:
                    raise EOFError(f"entry {entry.index} ended unexpectedly")
                output.write(chunk)
                remaining -= len(chunk)
                written += len(chunk)
            return written


def _read_exact(stream: BinaryIO, size: int) -> bytes:
    data = stream.read(size)
    if len(data) != size:
        raise EOFError(f"expected {size} bytes, got {len(data)}")
    return data


def _read_u32le(stream: BinaryIO, offset: int) -> int:
    stream.seek(offset)
    return struct.unpack("<I", _read_exact(stream, 4))[0]


def _read_u64le(stream: BinaryIO, offset: int) -> int:
    stream.seek(offset)
    return struct.unpack("<Q", _read_exact(stream, 8))[0]


def _entry_record(obb: Obb, stream: BinaryIO, entry: Entry, prefix: int) -> dict:
    entry_type = obb.type_bytes(stream, entry)
    record = {
        "index": entry.index,
        "hash": f"{entry.name_hash:08x}",
        "block": entry.block,
        "offset": entry.offset,
        "length": entry.length,
        "stored_size": obb.stored_size(entry),
        "type": TYPE_NAMES.get(entry_type, entry_type.hex()),
    }
    if prefix and entry_type in (TYPE_COMPRESSED, TYPE_ZLIB):
        data = obb.decompressed_prefix(stream, entry, prefix)
        record["decompressed_prefix_hex"] = data.hex()
        record["decompressed_prefix_ascii"] = "".join(
            chr(value) if 32 <= value <= 126 else "." for value in data
        )
    return record


def command_list(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    with obb.path.open("rb") as stream:
        type_counts: collections.Counter[str] = collections.Counter()
        for entry in obb.entries:
            entry_type = obb.type_bytes(stream, entry)
            type_counts[TYPE_NAMES.get(entry_type, entry_type.hex())] += 1

    print(
        json.dumps(
            {
                "archive": str(obb.path),
                "size": obb.path.stat().st_size,
                "entries": len(obb.entries),
                "types": dict(type_counts.most_common()),
            },
            indent=2,
        )
    )
    return 0


def command_show(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    if args.index < 0 or args.index >= len(obb.entries):
        raise IndexError(f"entry index must be between 0 and {len(obb.entries) - 1}")
    with obb.path.open("rb") as stream:
        print(
            json.dumps(
                _entry_record(obb, stream, obb.entries[args.index], args.prefix),
                indent=2,
            )
        )
    return 0


def command_extract(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    if args.index < 0 or args.index >= len(obb.entries):
        raise IndexError(f"entry index must be between 0 and {len(obb.entries) - 1}")
    entry = obb.entries[args.index]
    written = obb.extract(entry, args.output, args.decompress)
    print(f"wrote {written} bytes to {args.output}")
    return 0


def command_scan(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    needles = [needle.lower().encode("utf-8") for needle in args.text]
    results: list[dict] = []
    errors: list[dict] = []
    with obb.path.open("rb") as stream:
        for entry in obb.entries:
            if entry.block < args.min_block or entry.block > args.max_block:
                continue
            entry_type = obb.type_bytes(stream, entry)
            if entry_type not in (TYPE_COMPRESSED, TYPE_ZLIB):
                continue
            try:
                prefix = obb.decompressed_prefix(stream, entry, args.prefix)
            except (EOFError, ValueError, zlib.error) as error:
                errors.append({"index": entry.index, "error": str(error)})
                continue
            lowered = prefix.lower()
            matched = [text for text, needle in zip(args.text, needles) if needle in lowered]
            if matched:
                record = _entry_record(obb, stream, entry, 0)
                record["matched"] = matched
                record["prefix_ascii"] = "".join(
                    chr(value) if 32 <= value <= 126 else "." for value in prefix
                )
                results.append(record)
    print(json.dumps({"matches": results, "errors": errors}, indent=2))
    return 0


def command_signatures(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    signatures: dict[str, dict] = {}
    rows: list[dict] = []
    errors: list[dict] = []
    with obb.path.open("rb") as stream:
        for entry in obb.entries:
            if entry.block < args.min_block or entry.block > args.max_block:
                continue
            entry_type = obb.type_bytes(stream, entry)
            if entry_type not in (TYPE_COMPRESSED, TYPE_ZLIB):
                continue
            try:
                prefix = obb.decompressed_prefix(stream, entry, args.prefix)
            except (EOFError, ValueError, zlib.error) as error:
                errors.append({"index": entry.index, "error": str(error)})
                continue
            signature = prefix[:4].hex() if len(prefix) >= 4 else "short"
            group = signatures.setdefault(signature, {"count": 0, "examples": []})
            group["count"] += 1
            if len(group["examples"]) < args.examples:
                group["examples"].append(entry.index)
            if args.rows:
                rows.append(
                    {
                        "index": entry.index,
                        "hash": f"{entry.name_hash:08x}",
                        "block": entry.block,
                        "stored_length": entry.length,
                        "signature": signature,
                        "prefix_hex": prefix.hex(),
                    }
                )

    ordered = dict(
        sorted(signatures.items(), key=lambda item: (-item[1]["count"], item[0]))
    )
    print(json.dumps({"signatures": ordered, "rows": rows, "errors": errors}, indent=2))
    return 0


def command_strings(args: argparse.Namespace) -> int:
    data = args.input.read_bytes()
    results: list[dict] = []
    ascii_pattern = re.compile(rb"[\x20-\x7e]{" + str(args.minimum).encode() + rb",}")
    utf16_pattern = re.compile(
        rb"(?:[\x20-\x7e]\x00){" + str(args.minimum).encode() + rb",}"
    )
    for encoding, pattern in (("ascii", ascii_pattern), ("utf-16le", utf16_pattern)):
        for match in pattern.finditer(data):
            raw = match.group()
            text = raw.decode(encoding, errors="replace")
            if args.contains and args.contains.lower() not in text.lower():
                continue
            results.append(
                {"offset": match.start(), "encoding": encoding, "text": text}
            )
    results.sort(key=lambda row: row["offset"])
    print(json.dumps(results, indent=2))
    return 0


def command_layout(args: argparse.Namespace) -> int:
    data = args.input.read_bytes()
    runs: list[dict] = []
    start: int | None = None
    last = -1
    for index, value in enumerate(data):
        if value:
            if start is None:
                start = index
            last = index
        elif start is not None and index - last > args.zero_gap:
            runs.append({"start": start, "end": last + 1, "length": last + 1 - start})
            start = None
    if start is not None:
        runs.append({"start": start, "end": last + 1, "length": last + 1 - start})

    markers: list[dict] = []
    for label, marker in TYPE_NAMES.items():
        position = 0
        while True:
            position = data.find(label, position)
            if position < 0:
                break
            markers.append({"offset": position, "marker": marker})
            position += 1
    markers.sort(key=lambda row: row["offset"])
    print(json.dumps({"size": len(data), "nonzero_runs": runs, "markers": markers}, indent=2))
    return 0


def command_records(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    by_offset = sorted(obb.entries, key=lambda entry: (entry.block, entry.index))

    rows: list[dict] = []
    with obb.path.open("rb") as stream:
        for entry in by_offset:
            entry_type = obb.type_bytes(stream, entry)
            type_name = TYPE_NAMES.get(entry_type, entry_type.hex())
            if args.type and type_name != args.type:
                continue
            if entry.block < args.min_block or entry.block > args.max_block:
                continue
            rows.append(
                {
                    "index": entry.index,
                    "hash": f"{entry.name_hash:08x}",
                    "block": entry.block,
                    "field3": entry.length,
                    "type": type_name,
                    "bytes_to_next_entry": obb.stored_size(entry),
                }
            )
            if len(rows) >= args.limit:
                break
    print(json.dumps(rows, indent=2))
    return 0


def _dimension_hints(payload_size: int) -> list[str]:
    hints: list[str] = []
    dimensions = (64, 128, 256, 512, 1024, 2048, 4096)
    for width in dimensions:
        for height in dimensions:
            if width < height:
                continue
            pixels = width * height
            if payload_size == pixels:
                hints.append(f"{width}x{height}:8bpp")
            if payload_size * 2 == pixels:
                hints.append(f"{width}x{height}:4bpp")
            if payload_size == pixels * 4:
                hints.append(f"{width}x{height}:rgba32")
    return hints


def command_decompressed_records(args: argparse.Namespace) -> int:
    obb = Obb(args.obb)
    rows: list[dict] = []
    errors: list[dict] = []
    with obb.path.open("rb") as stream:
        for entry in sorted(obb.entries, key=lambda item: (item.block, item.index)):
            if entry.block < args.min_block or entry.block > args.max_block:
                continue
            entry_type = obb.type_bytes(stream, entry)
            if entry_type not in (TYPE_COMPRESSED, TYPE_ZLIB):
                continue
            try:
                total = 0
                prefix = bytearray()
                for chunk in obb.decompressed_chunks(stream, entry):
                    total += len(chunk)
                    if len(prefix) < args.prefix:
                        prefix.extend(chunk[: args.prefix - len(prefix)])
            except (EOFError, ValueError, zlib.error) as error:
                errors.append({"index": entry.index, "error": str(error)})
                continue
            if total < args.min_size or total > args.max_size:
                continue
            payload_size = total - args.header_size
            rows.append(
                {
                    "index": entry.index,
                    "hash": f"{entry.name_hash:08x}",
                    "block": entry.block,
                    "stored_size": obb.stored_size(entry),
                    "decompressed_size": total,
                    "signature": bytes(prefix[:4]).hex(),
                    "dimension_hints": _dimension_hints(payload_size),
                    "prefix_hex": bytes(prefix).hex(),
                }
            )
            if len(rows) >= args.limit:
                break
    print(json.dumps({"rows": rows, "errors": errors}, indent=2))
    return 0


def command_raw_find(args: argparse.Namespace) -> int:
    needles = {
        "ascii": args.text.encode("utf-8"),
        "utf-16le": args.text.encode("utf-16le"),
    }
    overlap = max(len(needle) for needle in needles.values()) - 1
    matches: list[dict] = []
    previous = b""
    absolute = 0
    with args.input.open("rb") as stream:
        while True:
            chunk = stream.read(args.chunk_size)
            if not chunk:
                break
            data = previous + chunk
            base = absolute - len(previous)
            for encoding, needle in needles.items():
                position = 0
                while True:
                    position = data.find(needle, position)
                    if position < 0:
                        break
                    offset = base + position
                    if not matches or not any(
                        row["offset"] == offset and row["encoding"] == encoding
                        for row in matches
                    ):
                        matches.append(
                            {"offset": offset, "encoding": encoding, "text": args.text}
                        )
                    position += 1
            absolute += len(chunk)
            previous = data[-overlap:] if overlap else b""
    matches.sort(key=lambda row: (row["offset"], row["encoding"]))
    print(json.dumps(matches, indent=2))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="summarize an OBB")
    list_parser.add_argument("obb", type=Path)
    list_parser.set_defaults(function=command_list)

    show_parser = subparsers.add_parser("show", help="show one entry")
    show_parser.add_argument("obb", type=Path)
    show_parser.add_argument("index", type=int)
    show_parser.add_argument("--prefix", type=int, default=128)
    show_parser.set_defaults(function=command_show)

    extract_parser = subparsers.add_parser("extract", help="extract one entry")
    extract_parser.add_argument("obb", type=Path)
    extract_parser.add_argument("index", type=int)
    extract_parser.add_argument("output", type=Path)
    extract_parser.add_argument("--decompress", action="store_true")
    extract_parser.set_defaults(function=command_extract)

    scan_parser = subparsers.add_parser(
        "scan", help="scan decompressed entry prefixes for text"
    )
    scan_parser.add_argument("obb", type=Path)
    scan_parser.add_argument("text", nargs="+")
    scan_parser.add_argument("--prefix", type=int, default=1024 * 1024)
    scan_parser.add_argument("--min-block", type=int, default=0)
    scan_parser.add_argument("--max-block", type=int, default=0xFFFFFFFF)
    scan_parser.set_defaults(function=command_scan)

    signature_parser = subparsers.add_parser(
        "signatures", help="group decompressed entries by their first four bytes"
    )
    signature_parser.add_argument("obb", type=Path)
    signature_parser.add_argument("--min-block", type=int, default=0)
    signature_parser.add_argument("--max-block", type=int, default=0xFFFFFFFF)
    signature_parser.add_argument("--prefix", type=int, default=64)
    signature_parser.add_argument("--examples", type=int, default=8)
    signature_parser.add_argument("--rows", action="store_true")
    signature_parser.set_defaults(function=command_signatures)

    strings_parser = subparsers.add_parser(
        "strings", help="list printable ASCII and UTF-16LE strings from a file"
    )
    strings_parser.add_argument("input", type=Path)
    strings_parser.add_argument("--minimum", type=int, default=4)
    strings_parser.add_argument("--contains")
    strings_parser.set_defaults(function=command_strings)

    layout_parser = subparsers.add_parser(
        "layout", help="show nonzero regions and known binary markers in a file"
    )
    layout_parser.add_argument("input", type=Path)
    layout_parser.add_argument("--zero-gap", type=int, default=64)
    layout_parser.set_defaults(function=command_layout)

    records_parser = subparsers.add_parser(
        "records", help="show directory records in physical block order"
    )
    records_parser.add_argument("obb", type=Path)
    records_parser.add_argument("--type")
    records_parser.add_argument("--min-block", type=int, default=0)
    records_parser.add_argument("--max-block", type=int, default=0xFFFFFFFF)
    records_parser.add_argument("--limit", type=int, default=100)
    records_parser.set_defaults(function=command_records)

    decompressed_parser = subparsers.add_parser(
        "decompressed-records", help="show decompressed size and header statistics"
    )
    decompressed_parser.add_argument("obb", type=Path)
    decompressed_parser.add_argument("--min-block", type=int, default=0)
    decompressed_parser.add_argument("--max-block", type=int, default=0xFFFFFFFF)
    decompressed_parser.add_argument("--min-size", type=int, default=0)
    decompressed_parser.add_argument("--max-size", type=int, default=0x7FFFFFFF)
    decompressed_parser.add_argument("--header-size", type=lambda value: int(value, 0), default=0xF0)
    decompressed_parser.add_argument("--prefix", type=int, default=208)
    decompressed_parser.add_argument("--limit", type=int, default=1000)
    decompressed_parser.set_defaults(function=command_decompressed_records)

    raw_find_parser = subparsers.add_parser(
        "raw-find", help="find ASCII or UTF-16LE text offsets in a large binary"
    )
    raw_find_parser.add_argument("input", type=Path)
    raw_find_parser.add_argument("text")
    raw_find_parser.add_argument("--chunk-size", type=int, default=16 * 1024 * 1024)
    raw_find_parser.set_defaults(function=command_raw_find)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        return args.function(args)
    except (EOFError, IndexError, OSError, ValueError, zlib.error) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

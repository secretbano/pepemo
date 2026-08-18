"""On-demand NBA 2K20 OBB editing without a full extraction workspace."""

from __future__ import annotations

import dataclasses
import hashlib
import json
import os
import struct
import zlib
from pathlib import Path

from nba2k20_obb import Obb, TYPE_COMPRESSED, TYPE_NAMES, TYPE_ZLIB
from obb_encrypt import (
    BINFILE_CHECKSUM_OFFSET,
    BuiltEntry,
    apply_entries,
    parse_entry,
    sha256_bytes,
    sha256_path,
    update_archive_crc32,
    verify_output,
)


KNOWN_NAMES = (
    "TITLEPAGE.IFF",
    "LOADINGFLOWSTATIC.IFF",
    "ENGLISHBOOTUP.IFF",
    "FRONTEND_SYNC.IFF",
    "GOOEYFRONTEND.IFF",
    "GLOBAL.IFF",
    "LOGOS_LARGE.CDF",
    "LOGOS_MEDIUM.CDF",
    "LOGOS_SMALL.CDF",
    "LOGOS_TINY.CDF",
    *(f"F{index:03d}.IFF" for index in range(32)),
    *(f"LOGO{index:03d}.IFF" for index in range(32)),
    *(f"UH{index:03d}.IFF" for index in range(32)),
    *(f"UA{index:03d}.IFF" for index in range(32)),
)
NAME_BY_HASH = {zlib.crc32(name.encode("ascii")): name for name in KNOWN_NAMES}
EDITABLE_TYPES = (TYPE_COMPRESSED, TYPE_ZLIB)
COPY_CHUNK = 16 * 1024 * 1024


@dataclasses.dataclass
class StagedEntry:
    index: int
    label: str
    raw_path: Path
    raw_size: int
    decompressed_size: int
    decompressed_sha256: str


class DirectObbSession:
    """One OBB plus a small cache containing only edited entry containers."""

    def __init__(self, path: Path, cache_dir: Path):
        self.path = path.resolve()
        if not self.path.is_file():
            raise ValueError(f"OBB was not found: {self.path}")
        self.obb = Obb(self.path)
        self.cache_dir = cache_dir.resolve()
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        stat = self.path.stat()
        self.source_size = stat.st_size
        self.source_modified_ns = stat.st_mtime_ns
        self.staged: dict[int, StagedEntry] = {}

    def _entry(self, index: int):
        if index < 0 or index >= len(self.obb.entries):
            raise IndexError(f"OBB entry index must be 0-{len(self.obb.entries) - 1}")
        return self.obb.entries[index]

    def entry_name(self, index: int) -> str:
        entry = self._entry(index)
        known = NAME_BY_HASH.get(entry.name_hash)
        return known or f"{entry.name_hash:08x}.iff"

    def entry_type(self, index: int) -> tuple[bytes, str]:
        entry = self._entry(index)
        with self.path.open("rb") as stream:
            marker = self.obb.type_bytes(stream, entry)
        return marker, TYPE_NAMES.get(marker, marker.hex())

    def rows(self) -> list[tuple]:
        rows: list[tuple] = []
        with self.path.open("rb") as stream:
            for entry in self.obb.entries:
                marker = self.obb.type_bytes(stream, entry)
                type_name = TYPE_NAMES.get(marker, marker.hex())
                known = NAME_BY_HASH.get(entry.name_hash)
                label = known or f"{entry.name_hash:08x}"
                rows.append(
                    (
                        entry.index,
                        label,
                        f"{entry.name_hash:08x}",
                        type_name,
                        entry.length,
                        self.obb.stored_size(entry),
                        entry.block,
                        entry.index in self.staged,
                        marker in EDITABLE_TYPES,
                    )
                )
        return rows

    def read_entry_raw(self, index: int) -> bytes:
        staged = self.staged.get(index)
        if staged is not None:
            return staged.raw_path.read_bytes()
        entry = self._entry(index)
        with self.path.open("rb") as stream:
            stream.seek(entry.offset)
            raw = stream.read(entry.length)
        if len(raw) != entry.length:
            raise EOFError(
                f"OBB entry {index} is truncated: expected {entry.length}, got {len(raw)}"
            )
        return raw

    def stage_iff(
        self,
        index: int,
        rebuilt_raw: bytes,
        decompressed_data: bytes,
        *,
        opaque_raw: bool = False,
    ) -> StagedEntry:
        entry = self._entry(index)
        marker, type_name = self.entry_type(index)
        if marker not in EDITABLE_TYPES:
            raise ValueError(f"entry {index} ({type_name}) is not a ZLIB/IFF entry")
        if opaque_raw:
            # Some older/alternate NBA 2K IFF containers use the same 94 EF 3B FF
            # wrapper but do not contain the newer ZLIB block records.  For those
            # containers the byte stream itself is the authoritative replacement;
            # the caller has already validated the legacy wrapper structure.
            check_data = rebuilt_raw
        else:
            check_data, _blocks, _first_offset, _compressed = parse_entry(
                rebuilt_raw, len(rebuilt_raw)
            )
            if bytes(check_data) != decompressed_data:
                raise ValueError(
                    f"entry {index} staging verification failed: decompressed bytes differ"
                )
        destination = self.cache_dir / f"entry_{index:04d}.rebuilt"
        temporary = destination.with_suffix(destination.suffix + ".partial")
        temporary.write_bytes(rebuilt_raw)
        os.replace(temporary, destination)
        staged = StagedEntry(
            index=index,
            label=self.entry_name(index),
            raw_path=destination,
            raw_size=len(rebuilt_raw),
            decompressed_size=(len(rebuilt_raw) if opaque_raw else len(decompressed_data)),
            decompressed_sha256=(
                hashlib.sha256(rebuilt_raw if opaque_raw else decompressed_data).hexdigest().upper()
            ),
        )
        self.staged[index] = staged
        return staged

    def discard_stage(self, index: int) -> None:
        staged = self.staged.pop(index, None)
        if staged is not None:
            staged.raw_path.unlink(missing_ok=True)

    def _assert_source_unchanged(self) -> None:
        stat = self.path.stat()
        if (stat.st_size, stat.st_mtime_ns) != (
            self.source_size,
            self.source_modified_ns,
        ):
            raise ValueError(
                "the source OBB changed outside the manager; reopen it before saving"
            )

    def _built_entries(self) -> list[BuiltEntry]:
        output: list[BuiltEntry] = []
        for index in sorted(self.staged):
            staged = self.staged[index]
            entry = self._entry(index)
            raw = staged.raw_path.read_bytes()
            mode = "preserved" if len(raw) <= self.obb.stored_size(entry) else "append"
            output.append(
                BuiltEntry(
                    name=staged.label,
                    index=index,
                    offset=entry.offset,
                    slot_size=self.obb.stored_size(entry),
                    data=raw,
                    expected_sha256=staged.decompressed_sha256,
                    expected_size=staged.decompressed_size,
                    is_zlib=True,
                    mode=mode,
                )
            )
        return output

    def save_obb(
        self,
        destination: Path,
        *,
        allow_overwrite: bool = False,
        progress=None,
    ) -> dict:
        def notify(message: str) -> None:
            if progress is not None:
                progress(message)

        if not self.staged:
            raise ValueError("no edited IFF entries are staged for the OBB")
        self._assert_source_unchanged()
        destination = destination.resolve()
        overwriting_source = destination == self.path
        if destination.exists() and not (allow_overwrite or overwriting_source):
            raise ValueError(f"output OBB already exists: {destination}")
        if overwriting_source and not allow_overwrite:
            raise ValueError("direct OBB overwrite requires explicit confirmation")
        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = destination.with_suffix(destination.suffix + ".partial")
        if temporary.exists():
            raise ValueError(f"temporary OBB output already exists: {temporary}")
        built_entries = self._built_entries()
        notify("Hashing source OBB ...")
        source_sha256 = sha256_path(self.path)
        try:
            notify("Copying archive and applying edited IFF entries ...")
            apply_entries(self.path, temporary, built_entries)
            notify("Calculating archive CRC32 ...")
            archive_crc32 = update_archive_crc32(temporary)
            notify("Verifying edited entries and complete archive CRC ...")
            verify_output(temporary, built_entries, archive_crc32)
            notify("Hashing verified output OBB ...")
            output_sha256 = sha256_path(temporary)
            output_size = temporary.stat().st_size
            notify("Installing verified OBB ...")
            os.replace(temporary, destination)
        finally:
            temporary.unlink(missing_ok=True)
        report = {
            "source_obb": str(self.path),
            "source_obb_sha256": source_sha256,
            "output_obb": str(destination),
            "output_obb_size": output_size,
            "output_obb_sha256": output_sha256,
            "archive_crc32": f"0x{archive_crc32:08X}",
            "changed_entry_count": len(built_entries),
            "changed_entries": [
                {
                    "index": item.index,
                    "name": item.name,
                    "mode": item.mode,
                    "decompressed_size": item.expected_size,
                    "decompressed_sha256": item.expected_sha256,
                }
                for item in built_entries
            ],
            "overwrote_source": overwriting_source,
            "verification": "PASS",
        }
        report_path = destination.with_suffix(destination.suffix + ".build_report.json")
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        report["report"] = str(report_path)
        if overwriting_source:
            # The new archive becomes the source baseline for later edits.
            self.obb = Obb(self.path)
            stat = self.path.stat()
            self.source_size = stat.st_size
            self.source_modified_ns = stat.st_mtime_ns
            for staged in self.staged.values():
                staged.raw_path.unlink(missing_ok=True)
            self.staged.clear()
        return report

from __future__ import annotations

import json
import base64
import os
import tempfile
from pathlib import Path

from PIL import Image

from obb_tools.direct_obb import DirectObbSession, EDITABLE_TYPES
from iff_viewer import (
    open_iff_bytes,
    decode_texture,
    decompress_wrapper,
    rebuild_compressed_iff,
    import_png,
    FORMAT_NAMES,
)
try:
    from etc2_repair import decode_etc2_auto
except Exception:
    decode_etc2_auto = None
from pure_etc2 import decode_etc2 as decode_etc2_pure, decode_etc2_rgba8 as decode_etc2_rgba8_pure

_session = None
_opened = None
_opened_index = None
_cache_root = None


def _json(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False)


def open_obb(path: str, cache_dir: str):
    global _session, _cache_root, _opened, _opened_index
    _cache_root = Path(cache_dir)
    _cache_root.mkdir(parents=True, exist_ok=True)
    _session = DirectObbSession(Path(path), _cache_root / "obb")
    _opened = None
    _opened_index = None
    return _json({"rows": _session.rows(), "count": len(_session.obb.entries)})


def close_obb():
    global _session, _opened, _opened_index
    _session = None
    _opened = None
    _opened_index = None


def obb_rows(query: str = ""):
    if _session is None:
        raise RuntimeError("No OBB is open")
    rows = _session.rows()
    q = (query or "").strip().lower()
    if not q:
        return _json(rows)
    out = []
    for row in rows:
        text = " ".join(str(x) for x in row).lower()
        if q in text:
            out.append(row)
    return _json(out)


def _ensure_entry(index: int):
    global _opened, _opened_index
    if _session is None:
        raise RuntimeError("No OBB is open")
    raw = _session.read_entry_raw(index)
    name = _session.entry_name(index)
    marker, type_name = _session.entry_type(index)
    if marker not in EDITABLE_TYPES:
        raise ValueError(f"Entry {index} is {type_name}; it is not an editable IFF container")
    _opened = open_iff_bytes(raw, Path(name), look_for_manifest=False)
    _opened_index = index
    return _opened


def open_entry(index: int):
    opened = _ensure_entry(int(index))
    return _json({
        "index": int(index),
        "name": _session.entry_name(int(index)),
        "summary": opened.summary(),
        "textures": [t.as_dict() for t in opened.textures],
    })


def texture_info():
    if _opened is None:
        raise RuntimeError("Open an IFF entry first")
    return _json([t.as_dict() for t in _opened.textures])


def _get_texture(number: int):
    if _opened is None:
        raise RuntimeError("Open an IFF entry first")
    for t in _opened.textures:
        if t.number == int(number):
            return t
    raise IndexError(f"Texture {number} not found")


def _decode_force_auto(texture):
    if texture.payload_offset is None:
        raise ValueError(texture.error or "texture payload location is unknown")
    start = texture.payload_offset
    payload = bytes(_opened.data[start:start + texture.payload_size])
    if texture.format_id not in (15, 16):
        return decode_texture(_opened, texture), "native"
    if decode_etc2_auto is None:
        return decode_texture(_opened, texture), "standard"
    rgba8 = texture.format_id == 16
    decoded, layout, score = decode_etc2_auto(
        payload, texture.width, texture.height,
        rgba8=rgba8, preferred_layout="standard", force=True,
    )
    image = Image.frombytes("RGBA", (texture.width, texture.height), decoded, "raw", "BGRA")
    texture.decode_layout = layout
    texture.decode_score = score
    return image, layout


def decode_texture_rgba(number: int, force_auto: bool = False):
    texture = _get_texture(int(number))
    image, layout = _decode_force_auto(texture) if force_auto else (decode_texture(_opened, texture), getattr(texture, "decode_layout", "standard"))
    try:
        rgba = image.tobytes("raw", "RGBA")
        result = {
            "width": image.width,
            "height": image.height,
            "format": FORMAT_NAMES.get(texture.format_id, str(texture.format_id)),
            "layout": layout,
            "score": getattr(texture, "decode_score", None),
            "rgba": rgba,
        }
        return result
    finally:
        image.close()



def decode_texture_base64(number: int, force_auto: bool = False):
    result = decode_texture_rgba(int(number), force_auto)
    return _json({
        "width": result["width"],
        "height": result["height"],
        "format": result["format"],
        "layout": result["layout"],
        "score": result["score"],
        "rgba_b64": base64.b64encode(result["rgba"]).decode("ascii"),
    })

def texture_meta(number: int):
    t = _get_texture(int(number))
    return _json(t.as_dict())


def extract_entry(index: int, destination: str):
    if _session is None:
        raise RuntimeError("No OBB is open")
    raw = _session.read_entry_raw(int(index))
    p = Path(destination)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(raw)
    return _json({"path": str(p), "size": len(raw), "name": _session.entry_name(int(index))})


def extract_texture_png(number: int, destination: str, force_auto: bool = False):
    result = decode_texture_rgba(int(number), force_auto)
    image = Image.frombytes("RGBA", (result["width"], result["height"]), result["rgba"])
    p = Path(destination)
    p.parent.mkdir(parents=True, exist_ok=True)
    image.save(p, format="PNG", optimize=False)
    image.close()
    return _json({"path": str(p), "width": result["width"], "height": result["height"], "layout": result["layout"]})


def import_texture_png(number: int, png_path: str):
    if _opened is None or _opened_index is None:
        raise RuntimeError("Open an IFF entry first")
    t = _get_texture(int(number))
    report = import_png(_opened, t, Path(png_path))
    rebuilt, mode, changed_blocks = rebuild_compressed_iff(_opened)
    _session.stage_iff(_opened_index, rebuilt, bytes(_opened.data), opaque_raw=(mode == "decompressed"))
    return _json({"import": report, "container_mode": mode, "changed_blocks": changed_blocks, "staged": True})


def replace_ascii(find_text: str, replace_text: str):
    if _opened is None or _opened_index is None:
        raise RuntimeError("Open an IFF entry first")
    a = find_text.encode("utf-8")
    b = replace_text.encode("utf-8")
    if not a:
        raise ValueError("Find text cannot be empty")
    if len(a) != len(b):
        raise ValueError(f"Replacement must be the same byte length ({len(a)} bytes)")
    data = _opened.data
    positions = []
    pos = 0
    while True:
        pos = data.find(a, pos)
        if pos < 0:
            break
        positions.append(pos)
        pos += len(a)
    if not positions:
        raise ValueError("Text not found")
    for pos in positions:
        data[pos:pos + len(a)] = b
    rebuilt, mode, changed_blocks = rebuild_compressed_iff(_opened)
    _session.stage_iff(_opened_index, rebuilt, bytes(_opened.data), opaque_raw=(mode == "decompressed"))
    return _json({"replaced": len(positions), "container_mode": mode, "changed_blocks": changed_blocks})


def strings_preview(max_bytes: int = 65536):
    if _opened is None:
        raise RuntimeError("Open an IFF entry first")
    data = bytes(_opened.data[:max_bytes])
    lines = []
    start = None
    for i, c in enumerate(data):
        printable = 32 <= c <= 126 or c in (9,)
        if printable:
            if start is None:
                start = i
        elif start is not None:
            if i - start >= 4:
                raw = data[start:i]
                try:
                    text = raw.decode("ascii")
                except Exception:
                    text = ""
                if text:
                    lines.append(f"0x{start:X}: {text}")
            start = None
    if start is not None and len(data) - start >= 4:
        lines.append(f"0x{start:X}: {data[start:].decode('ascii', 'ignore')}")
    return "\n".join(lines[:2000])


def save_obb(destination: str):
    if _session is None:
        raise RuntimeError("No OBB is open")
    return _json(_session.save_obb(Path(destination), allow_overwrite=False))


def staged_count():
    return len(_session.staged) if _session is not None else 0

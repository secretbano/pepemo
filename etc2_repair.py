"""Android/Pydroid ETC2 layout repair helper.

Some mobile game texture banks are presented to the editor with a block layout
that is not the normal row-major ETC2 order.  The ETC2 bitstream itself is
valid; the problem is which 4x4 compressed block is placed at each image block.
This module keeps the normal decoder untouched and tries a small set of common
block layouts, selecting a layout with the best block-edge continuity score.
"""
from __future__ import annotations

from math import log2

from pure_etc2 import decode_etc2_block, _decode_alpha_block


def _morton2(x: int, y: int) -> int:
    out = 0
    bit = 0
    while (1 << bit) <= max(x, y):
        out |= ((x >> bit) & 1) << (2 * bit)
        out |= ((y >> bit) & 1) << (2 * bit + 1)
        bit += 1
    return out


def _layout_source(name: str, ox: int, oy: int, bw: int, bh: int) -> tuple[int, int] | None:
    if name == "standard":
        return ox, oy
    if name == "flip-x":
        return bw - 1 - ox, oy
    if name == "flip-y":
        return ox, bh - 1 - oy
    if name == "flip-xy":
        return bw - 1 - ox, bh - 1 - oy
    if name == "transpose":
        if bw != bh:
            return None
        return oy, ox
    if name in ("morton", "morton-reverse"):
        if bw != bh or bw <= 0 or (bw & (bw - 1)):
            return None
        linear = _morton2(ox, oy)
        if name == "morton-reverse":
            linear = bw * bh - 1 - linear
        return linear % bw, linear // bw
    if name == "tile2x2":
        # Swap the order of 2x2 compressed-block tiles while retaining the
        # pixels inside each tile. This is a common lightweight mobile layout.
        tx, ty = ox // 2, oy // 2
        ix, iy = ox & 1, oy & 1
        tiles_w = (bw + 1) // 2
        tiles_h = (bh + 1) // 2
        linear = ty * tiles_w + tx
        rev = tiles_w * tiles_h - 1 - linear
        stx, sty = rev % tiles_w, rev // tiles_w
        sx, sy = stx * 2 + ix, sty * 2 + iy
        if sx >= bw or sy >= bh:
            return None
        return sx, sy
    return None


LAYOUTS = ("standard", "flip-x", "flip-y", "flip-xy", "transpose", "morton", "morton-reverse", "tile2x2")


def _decode_block(payload: bytes, bx: int, by: int, bw: int, bh: int, rgba8: bool, layout: str) -> bytes | None:
    src = _layout_source(layout, bx, by, bw, bh)
    if src is None:
        return None
    sx, sy = src
    index = sy * bw + sx
    stride = 16 if rgba8 else 8
    start = index * stride
    if start + stride > len(payload):
        return None
    if rgba8:
        alpha = _decode_alpha_block(payload[start:start + 8])
        color = decode_etc2_block(payload[start + 8:start + 16])
        out = bytearray(64)
        for i in range(16):
            p = i * 4
            out[p:p + 4] = color[p:p + 3] + bytes((alpha[i],))
        return bytes(out)
    return decode_etc2_block(payload[start:start + 8])


def _edge_score(payload: bytes, width: int, height: int, rgba8: bool, layout: str, sample_blocks: int = 12) -> float:
    bw = (width + 3) // 4
    bh = (height + 3) // 4
    # Sample a regular grid across the texture. We compare the touching edge
    # of neighboring blocks. A correct layout tends to have lower discontinuity
    # than a scrambled block order, even for detailed atlases.
    xs = sorted(set(min(bw - 1, int(i * (bw - 1) / max(1, sample_blocks - 1))) for i in range(sample_blocks)))
    ys = sorted(set(min(bh - 1, int(i * (bh - 1) / max(1, sample_blocks - 1))) for i in range(sample_blocks)))
    blocks: dict[tuple[int, int], bytes] = {}
    for y in ys:
        for x in xs:
            block = _decode_block(payload, x, y, bw, bh, rgba8, layout)
            if block is not None:
                blocks[x, y] = block
    if not blocks:
        return float("inf")
    total = 0.0
    count = 0
    for (x, y), a in blocks.items():
        if (x + 1, y) in blocks:
            b = blocks[x + 1, y]
            for row in range(4):
                pa = (row * 4 + 3) * 4
                pb = (row * 4) * 4
                total += sum(abs(a[pa + c] - b[pb + c]) for c in range(3)) / 3.0
                count += 1
        if (x, y + 1) in blocks:
            b = blocks[x, y + 1]
            for col in range(4):
                pa = (3 * 4 + col) * 4
                pb = col * 4
                total += sum(abs(a[pa + c] - b[pb + c]) for c in range(3)) / 3.0
                count += 1
    return total / max(1, count)


def _decode_full(payload: bytes, width: int, height: int, rgba8: bool, layout: str) -> bytes:
    bw = (width + 3) // 4
    bh = (height + 3) // 4
    out = bytearray(width * height * 4)
    for by in range(bh):
        for bx in range(bw):
            block = _decode_block(payload, bx, by, bw, bh, rgba8, layout)
            if block is None:
                raise ValueError(f"ETC2 layout {layout} cannot map {width}x{height}")
            for y in range(4):
                yy = by * 4 + y
                if yy >= height:
                    break
                src = y * 16
                dst = (yy * width + bx * 4) * 4
                count = min(4, width - bx * 4)
                out[dst:dst + count * 4] = block[src:src + count * 4]
    return bytes(out)


def decode_etc2_layout(payload: bytes, width: int, height: int, *, rgba8: bool = False, layout: str = "standard") -> bytes:
    return _decode_full(payload, width, height, rgba8, layout)


def decode_etc2_auto(
    payload: bytes,
    width: int,
    height: int,
    *,
    rgba8: bool = False,
    preferred_layout: str = "standard",
    force: bool = False,
):
    stride = 16 if rgba8 else 8
    need = ((width + 3) // 4) * ((height + 3) // 4) * stride
    if len(payload) < need:
        raise ValueError(f"ETC2 payload is too small: {len(payload)} < {need}")

    if not force and preferred_layout not in ("", "standard"):
        return _decode_full(payload, width, height, rgba8, preferred_layout), preferred_layout, 0.0

    candidates = []
    for layout in LAYOUTS:
        score = _edge_score(payload, width, height, rgba8, layout)
        if score != float("inf"):
            candidates.append((score, layout))
    if not candidates:
        raise ValueError("No usable ETC2 block layout was found")
    candidates.sort(key=lambda item: item[0])
    best_score, best_layout = candidates[0]
    # Do not flip a clearly valid standard texture for a tiny numerical gain.
    standard = next((score for score, name in candidates if name == "standard"), best_score)
    if best_layout != "standard" and best_score > standard * 0.70:
        best_layout = "standard"
        best_score = standard
    return _decode_full(payload, width, height, rgba8, best_layout), best_layout, float(best_score)

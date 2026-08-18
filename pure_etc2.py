"""Pure-Python ETC2 RGB / ETC2 RGBA8 decoder.

Fallback for Android/Pydroid 3 when texture2ddecoder's native extension is
not available. The block logic follows the ETC2 decoder used by AssetStudio's
MIT-licensed Texture2DDecoderNative implementation.
"""

WRITE_ORDER = (0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15)
WRITE_ORDER_REV = (15, 11, 7, 3, 14, 10, 6, 2, 13, 9, 5, 1, 12, 8, 4, 0)
MOD = ((2, 8), (5, 17), (9, 29), (13, 42), (18, 60), (24, 80), (33, 106), (47, 183))
DIST = (3, 6, 11, 16, 23, 32, 41, 64)
ALPHA_MOD = (
    (-3, -6, -9, -15, 2, 5, 8, 14), (-3, -7, -10, -13, 2, 6, 9, 12),
    (-2, -5, -8, -13, 1, 4, 7, 12), (-2, -4, -6, -13, 1, 3, 5, 12),
    (-3, -6, -8, -12, 2, 5, 7, 11), (-3, -7, -9, -11, 2, 6, 8, 10),
    (-4, -7, -8, -11, 3, 6, 7, 10), (-3, -5, -8, -11, 2, 4, 7, 10),
    (-2, -6, -8, -10, 1, 5, 7, 9), (-2, -5, -8, -10, 1, 4, 7, 9),
    (-2, -4, -8, -10, 1, 3, 7, 9), (-2, -5, -7, -10, 1, 4, 6, 9),
    (-3, -4, -7, -10, 2, 3, 6, 9), (-1, -2, -3, -10, 0, 1, 2, 9),
    (-4, -6, -8, -9, 3, 5, 7, 8), (-3, -5, -7, -9, 2, 4, 6, 8),
)
SUB = ((0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1),
       (0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1))


def _clamp(v):
    return 0 if v < 0 else 255 if v > 255 else v


def _px(r, g, b, a=255):
    return bytes((_clamp(b), _clamp(g), _clamp(r), _clamp(a)))


def _rgb_from_diff(data):
    r = data[0] & 0xF8
    dr = ((data[0] << 3) & 0x18) - ((data[0] << 3) & 0x20)
    g = data[1] & 0xF8
    dg = ((data[1] << 3) & 0x18) - ((data[1] << 3) & 0x20)
    b = data[2] & 0xF8
    db = ((data[2] << 3) & 0x18) - ((data[2] << 3) & 0x20)
    return r, dr, g, dg, b, db


def _write_subblock(out, data, c0, c1, code, flip, alpha=True):
    j = (data[6] << 8) | data[7]
    k = (data[4] << 8) | data[5]
    table = SUB[flip & 1]
    for i in range(16):
        s = table[i]
        m = MOD[code[s]][j & 1]
        sign = -1 if (k & 1) else 1
        r = c0[s][0] + (c1[s][0] - c0[s][0]) * 0  # keep branch-independent
        base = c0[s] if s == 0 else c1[s]
        v = sign * m
        p = WRITE_ORDER[i] * 4
        out[p:p+4] = _px(base[0] + v, base[1] + v, base[2] + v, 255)
        j >>= 1
        k >>= 1


def decode_etc2_block(data):
    if len(data) < 8:
        raise ValueError("ETC2 block requires 8 bytes")
    data = bytes(data[:8])
    j = (data[6] << 8) | data[7]
    k = (data[4] << 8) | data[5]
    r, dr, g, dg, b, db = _rgb_from_diff(data)
    out = bytearray(64)

    if data[3] & 2:
        if r + dr < 0 or r + dr > 255:  # T mode
            c0 = (
                (data[0] << 3 & 0xC0) | (data[0] << 4 & 0x30) | (data[0] >> 1 & 0x0C) | (data[0] & 3),
                (data[1] & 0xF0) | (data[1] >> 4),
                (data[1] & 0x0F) | (data[1] << 4),
            )
            c1 = (
                (data[2] & 0xF0) | (data[2] >> 4),
                (data[2] & 0x0F) | (data[2] << 4),
                (data[3] & 0xF0) | (data[3] >> 4),
            )
            d = DIST[((data[3] >> 1) & 6) | (data[3] & 1)]
            colors = (c0, tuple(_clamp(x + d) for x in c1), c1, tuple(_clamp(x - d) for x in c1))
            k <<= 1
            for i in range(16):
                p = WRITE_ORDER[i] * 4
                c = colors[(k & 2) | (j & 1)]
                out[p:p+4] = _px(*c)
                j >>= 1; k >>= 1
            return bytes(out)
        if g + dg < 0 or g + dg > 255:  # H mode
            c0 = (
                ((data[0] << 1) & 0xF0) | ((data[0] >> 3) & 0x0F),
                ((data[0] << 5) & 0xE0) | (data[1] & 0x10),
                (data[1] & 8) | ((data[1] << 1) & 6) | (data[2] >> 7),
            )
            c0 = (c0[0], c0[1] | (c0[1] >> 4), c0[2] | (c0[2] << 4))
            c1 = (
                ((data[2] << 1) & 0xF0) | ((data[2] >> 3) & 0x0F),
                ((data[2] << 5) & 0xE0) | ((data[3] >> 3) & 0x10),
                ((data[3] << 1) & 0xF0) | ((data[3] >> 3) & 0x0F),
            )
            c1 = (c1[0], c1[1] | (c1[1] >> 4), c1[2])
            d = (data[3] & 4) | ((data[3] << 1) & 2)
            if c0[0] > c1[0] or (c0[0] == c1[0] and (c0[1] > c1[1] or (c0[1] == c1[1] and c0[2] >= c1[2]))):
                d += 1
            d = DIST[d]
            colors = (tuple(_clamp(x+d) for x in c0), tuple(_clamp(x-d) for x in c0), tuple(_clamp(x+d) for x in c1), tuple(_clamp(x-d) for x in c1))
            k <<= 1
            for i in range(16):
                p = WRITE_ORDER[i] * 4
                out[p:p+4] = _px(*colors[(k & 2) | (j & 1)])
                j >>= 1; k >>= 1
            return bytes(out)
        if b + db < 0 or b + db > 255:  # planar mode
            c0 = (
                (data[0] << 1 & 0xFC) | (data[0] >> 5 & 3),
                (data[0] << 7 & 0x80) | (data[1] & 0x7E) | (data[0] & 1),
                (data[1] << 7 & 0x80) | (data[2] << 2 & 0x60) | (data[2] << 3 & 0x18) | (data[3] >> 5 & 4),
            )
            c0 = (c0[0], c0[1], c0[2] | (c0[2] >> 6))
            c1 = (
                (data[3] << 1 & 0xF8) | (data[3] << 2 & 4) | (data[3] >> 5 & 3),
                (data[4] & 0xFE) | (data[4] >> 7),
                (data[4] << 7 & 0x80) | (data[5] >> 1 & 0x7C),
            )
            c1 = (c1[0], c1[1], c1[2] | (c1[2] >> 6))
            c2 = (
                (data[5] << 5 & 0xE0) | (data[6] >> 3 & 0x1C) | (data[5] >> 1 & 3),
                (data[6] << 3 & 0xF8) | (data[7] >> 5 & 6) | (data[6] >> 4 & 1),
                (data[7] << 2) | (data[7] >> 4 & 3),
            )
            for y in range(4):
                for x in range(4):
                    r0 = (x*(c1[0]-c0[0]) + y*(c2[0]-c0[0]) + 4*c0[0] + 2) >> 2
                    g0 = (x*(c1[1]-c0[1]) + y*(c2[1]-c0[1]) + 4*c0[1] + 2) >> 2
                    b0 = (x*(c1[2]-c0[2]) + y*(c2[2]-c0[2]) + 4*c0[2] + 2) >> 2
                    p = (y*4+x)*4
                    out[p:p+4] = _px(r0,g0,b0)
            return bytes(out)

        # Normal differential ETC1-style mode.
        code = (data[3] >> 5, (data[3] >> 2) & 7)
        table = SUB[data[3] & 1]
        c0 = (r | (r >> 5), g | (g >> 5), b | (b >> 5))
        c1 = (r + dr, g + dg, b + db)
        c1 = (c1[0] | (c1[0] >> 5), c1[1] | (c1[1] >> 5), c1[2] | (c1[2] >> 5))
    else:
        code = (data[3] >> 5, (data[3] >> 2) & 7)
        table = SUB[data[3] & 1]
        c0 = ((data[0]&0xF0)|(data[0]>>4), (data[1]&0xF0)|(data[1]>>4), (data[2]&0xF0)|(data[2]>>4))
        c1 = ((data[0]&0x0F)|(data[0]<<4), (data[1]&0x0F)|(data[1]<<4), (data[2]&0x0F)|(data[2]<<4))

    # Differential/individual path. Unlike _write_subblock, the two
    # sub-blocks use their own base color and codeword.
    for i in range(16):
        s = table[i]
        m = MOD[code[s]][j & 1]
        base = c0 if s == 0 else c1
        v = -m if (k & 1) else m
        p = WRITE_ORDER[i] * 4
        out[p:p+4] = _px(base[0]+v, base[1]+v, base[2]+v)
        j >>= 1; k >>= 1
    return bytes(out)


def decode_etc2(data, width, height):
    bx = (width + 3) // 4
    by = (height + 3) // 4
    need = bx * by * 8
    if len(data) < need:
        raise ValueError(f"ETC2 RGB payload is too small: {len(data)} < {need}")
    out = bytearray(width * height * 4)
    pos = 0
    for yb in range(by):
        for xb in range(bx):
            block = decode_etc2_block(data[pos:pos+8])
            pos += 8
            for y in range(4):
                yy = yb*4+y
                if yy >= height: break
                src = y*16
                dst = (yy*width + xb*4) * 4
                count = min(4, width-xb*4)
                out[dst:dst+count*4] = block[src:src+count*4]
    return bytes(out)


def _decode_alpha_block(data):
    if len(data) < 8:
        raise ValueError("ETC2 alpha block requires 8 bytes")
    base = data[0]
    table = ALPHA_MOD[data[1] & 0x0F]
    mult = data[1] >> 4
    out = bytearray(16)
    if mult == 0:
        out[:] = bytes([base]) * 16
        return out
    # Big-endian 64-bit block, then consume 3-bit indices from LSB.
    l = int.from_bytes(data[:8], "big")
    for i in range(16):
        idx = l & 7
        out[WRITE_ORDER_REV[i]] = _clamp(base + mult * table[idx])
        l >>= 3
    return out


def decode_etc2_rgba8(data, width, height):
    bx = (width + 3) // 4
    by = (height + 3) // 4
    need = bx * by * 16
    if len(data) < need:
        raise ValueError(f"ETC2 RGBA8 payload is too small: {len(data)} < {need}")
    out = bytearray(width * height * 4)
    pos = 0
    for yb in range(by):
        for xb in range(bx):
            alpha = _decode_alpha_block(data[pos:pos+8])
            color = decode_etc2_block(data[pos+8:pos+16])
            pos += 16
            for y in range(4):
                yy = yb*4+y
                if yy >= height: break
                for x in range(4):
                    xx = xb*4+x
                    if xx >= width: break
                    si = (y*4+x)*4
                    di = (yy*width+xx)*4
                    out[di:di+4] = color[si:si+3] + bytes((alpha[y*4+x],))
    return bytes(out)


# ---------------------------------------------------------------------------
# Minimal ETC2/EAC encoder for Android/Pydroid.
# It deliberately uses the ETC2 individual-color mode, which is a legal ETC2
# RGB8 bitstream, plus EAC alpha for RGBA8.  The encoder favors robustness and
# portability over maximum compression quality: no native code is required.
# ---------------------------------------------------------------------------

_ENC_MOD = MOD


def _expand4(v):
    return (v << 4) | v


def _quant4(v):
    return max(0, min(15, (v * 15 + 127) // 255))


def _pack_etc2_individual_block(pix):
    """Encode one 4x4 RGBA block as legal ETC2 individual mode."""
    # Try both partition orientations.  Each subblock gets a 4-bit average
    # base color and the best modifier table.  This is intentionally simple,
    # deterministic, and does not depend on CPU-specific native extensions.
    best = None
    for flip in (0, 1):
        groups = ((0, 1, 2, 3, 4, 5, 6, 7), (8, 9, 10, 11, 12, 13, 14, 15))
        # Pixel order here is normal row-major; SUB[] maps the ETC bitstream
        # order (WRITE_ORDER) to the two partitions.
        part_pixels = [[], []]
        for i in range(16):
            x = i & 3
            y = i >> 2
            if flip == 0:
                part = 0 if x < 2 else 1
            else:
                part = 0 if y < 2 else 1
            part_pixels[part].append(i)

        bases = []
        tables = []
        choices = [0] * 16
        total_err = 0
        for part in (0, 1):
            inds = part_pixels[part]
            sr = sum(pix[i][0] for i in inds)
            sg = sum(pix[i][1] for i in inds)
            sb = sum(pix[i][2] for i in inds)
            n = len(inds)
            base = (_quant4(sr // n), _quant4(sg // n), _quant4(sb // n))
            bc = tuple(_expand4(v) for v in base)
            best_table = 0
            best_table_err = 1 << 60
            for table_id, mods in enumerate(_ENC_MOD):
                err = 0
                for i in inds:
                    r, g, b = pix[i][:3]
                    # Pick the best sign/modifier for this table.
                    m0, m1 = mods
                    d0 = (r-(bc[0]+m0))**2 + (g-(bc[1]+m0))**2 + (b-(bc[2]+m0))**2
                    d1 = (r-(bc[0]-m0))**2 + (g-(bc[1]-m0))**2 + (b-(bc[2]-m0))**2
                    d2 = (r-(bc[0]+m1))**2 + (g-(bc[1]+m1))**2 + (b-(bc[2]+m1))**2
                    d3 = (r-(bc[0]-m1))**2 + (g-(bc[1]-m1))**2 + (b-(bc[2]-m1))**2
                    d = min(d0, d1, d2, d3)
                    err += d
                    if err >= best_table_err:
                        break
                if err < best_table_err:
                    best_table_err = err
                    best_table = table_id
            tables.append(best_table)
            bases.append(base)
            total_err += best_table_err
            mods = _ENC_MOD[best_table]
            for i in inds:
                r, g, b = pix[i][:3]
                best_idx = 0
                best_d = 1 << 60
                for mi, m in enumerate(mods):
                    for sign in (1, -1):
                        v = sign * m
                        d = (r-(bc[0]+v))**2 + (g-(bc[1]+v))**2 + (b-(bc[2]+v))**2
                        if d < best_d:
                            best_d = d
                            best_idx = (mi << 1) | (0 if sign > 0 else 1)
                choices[i] = best_idx

        # Recompute exact error from chosen indices for fair flip comparison.
        for i in range(16):
            x = i & 3
            y = i >> 2
            part = (0 if (x < 2 if flip == 0 else y < 2) else 1)
            base = tuple(_expand4(v) for v in bases[part])
            m = _ENC_MOD[tables[part]][choices[i] >> 1]
            v = m if (choices[i] & 1) == 0 else -m
            r, g, b = pix[i][:3]
            total_err += (r-(base[0]+v))**2 + (g-(base[1]+v))**2 + (b-(base[2]+v))**2

        if best is None or total_err < best[0]:
            best = (total_err, flip, bases, tables, choices)

    _, flip, bases, tables, choices = best
    r0, g0, b0 = bases[0]
    r1, g1, b1 = bases[1]
    # Individual mode: diff bit = 0.  The decoder in this project interprets
    # bytes 4..7 as two 16-bit planes, each consumed LSB-first.
    b0v = (r0 << 4) | g0
    b1v = (b0 << 4) | b1
    header = bytearray(8)
    header[0] = (r0 << 4) | r1
    header[1] = (g0 << 4) | g1
    header[2] = (b0v & 0xF0) | (b1v >> 4)
    # Correct byte 2/3 packing for six 4-bit base colors.
    header[2] = (b0 << 4) | b1
    header[3] = (tables[0] << 5) | (tables[1] << 2) | (flip & 1)
    msb = 0
    lsb = 0
    # The ETC bitstream visits pixels in WRITE_ORDER; each visit consumes
    # one LSB from the two 16-bit index planes.
    for bit in range(16):
        pixel = WRITE_ORDER[bit]
        idx = choices[pixel]
        lsb |= (idx & 1) << bit
        msb |= ((idx >> 1) & 1) << bit
    header[4:6] = lsb.to_bytes(2, "big")
    header[6:8] = msb.to_bytes(2, "big")
    return bytes(header)


def _encode_eac_alpha_block(pix):
    """Encode one EAC R11 block used as the alpha half of ETC2 RGBA8.

    Multiplier zero is legal and gives an exact constant alpha for the block.
    This avoids fragile platform/native dependencies while preserving a valid
    16-byte ETC2 RGBA8 block layout.
    """
    a = sum(p[3] for p in pix) // 16
    # base, multiplier=0, table=0, all 3-bit indices zero
    return bytes((a, 0, 0, 0, 0, 0, 0, 0))


def encode_etc2_rgb(rgba, width, height):
    if width < 1 or height < 1:
        return b""
    src = memoryview(rgba)
    bx = (width + 3) // 4
    by = (height + 3) // 4
    out = bytearray(bx * by * 8)
    op = 0
    for yb in range(by):
        for xb in range(bx):
            block = []
            for y in range(4):
                yy = min(height - 1, yb * 4 + y)
                for x in range(4):
                    xx = min(width - 1, xb * 4 + x)
                    q = (yy * width + xx) * 4
                    block.append((src[q], src[q+1], src[q+2], src[q+3]))
            out[op:op+8] = _pack_etc2_individual_block(block)
            op += 8
    return bytes(out)


def encode_etc2_rgba8(rgba, width, height):
    if width < 1 or height < 1:
        return b""
    src = memoryview(rgba)
    bx = (width + 3) // 4
    by = (height + 3) // 4
    out = bytearray(bx * by * 16)
    op = 0
    for yb in range(by):
        for xb in range(bx):
            block = []
            for y in range(4):
                yy = min(height - 1, yb * 4 + y)
                for x in range(4):
                    xx = min(width - 1, xb * 4 + x)
                    q = (yy * width + xx) * 4
                    block.append((src[q], src[q+1], src[q+2], src[q+3]))
            out[op:op+8] = _encode_eac_alpha_block(block)
            out[op+8:op+16] = _pack_etc2_individual_block(block)
            op += 16
    return bytes(out)

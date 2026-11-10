from snark_lib import *

DOMAIN = DOMAIN_PLACEHOLDER
LENGTHS = LENGTHS_PLACEHOLDER
MPLEN = MPLEN_PLACEHOLDER
CTXLEN = CTXLEN_PLACEHOLDER
CLAIMCELLS = 2 + (MPLEN + 15) // 16
PADLAST = 9223372036854775808


def shake(data, length: Const):
    # StackBuf sizes are parsed before Const specialization; this covers the API's 8192-byte message cap.
    padded = StackBuf(536)
    for i in unroll(0, ((136 * (length // 136 + 1) + 15) // 16)):
        if const(i // ((length + 15) // 16) == 0):
            value = data[GEN ** i]
        else:
            value = 0
        if const(i == length // 16):
            value += const(31 * 2 ** (8 * (length % 16)))
        if const(i == (136 * (length // 136 + 1) - 1) // 16):
            value += const(128 * 2 ** (8 * ((136 * (length // 136 + 1) - 1) % 16)))
        padded[i] = value
    out = StackBuf(13)
    if const((length // 136 + 1) % 2 == 0):
        keccak_cells(padded[0:((136 * (length // 136 + 1) + 15) // 16)], out, final=0)
    else:
        state = StackBuf(13)
        if const(length // 136 != 0):
            keccak_cells(padded[0:17 * ((length // 136 + 1) // 2)], state, final=0)
        else:
            for i in unroll(0, 13):
                state[i] = 0
        last = StackBuf(13)
        for i in unroll(0, 9):
            last[i] = state[i] + padded[17 * ((length // 136 + 1) // 2) + i]
        for i in unroll(9, 13):
            last[i] = state[i]
        keccak(last[0:2], last[2:4], out, tail=last[4:8], cap=last)
    return out[0], out[1]


def f(pp, a0, a1, node):
    cap = StackBuf(13)
    cap[8] = PADLAST
    for i in unroll(9, 13):
        cap[i] = 0
    out = StackBuf(13)
    keccak([pp, a0], [a1, node], out, tail=[31, 0, 0, 0], cap=cap)
    return out[0]


def h(pp, a0, a1, node, sibling, bit):
    left = node + bit * (node + sibling)
    right = left + node + sibling
    cap = StackBuf(13)
    cap[8] = PADLAST
    for i in unroll(9, 13):
        cap[i] = 0
    out = StackBuf(13)
    keccak([pp, a0], [a1, left], out, tail=[right, 31, 0, 0], cap=cap)
    return out[0]


def fors_tree(pp, a0, key, bits: StackBuf(12), tree: Const):
    index = const(tree * 2 ** 116)
    for b in unroll(0, 12):
        index += const(2 ** (96 + 8 * (3 - b // 8) + b % 8)) * bits[b]
    secret = hint_witness("fors_secret")
    node = f(pp, a0, key + const(3 * 2 ** 24) + index, secret)
    for level in unroll(0, 12):
        # The tree offset participates in the global FORS node index at every height.
        idx = 0
        for b in unroll(0, 4):
            if const((tree // 2 ** b) % 2 == 1):
                idx += const(2 ** (96 + 8 * (3 - (12 - level - 1 + b) // 8) + (12 - level - 1 + b) % 8))
        for b in unroll(level + 1, 12):
            idx += const(2 ** (96 + 8 * (3 - (b - level - 1) // 8) + (b - level - 1) % 8)) * bits[b]
        sibling = hint_witness("fors_sibling")
        node = h(pp, a0, key + const(3 * 2 ** 24 + (level + 1) * 2 ** 88) + idx, node, sibling, bits[level])
    return node


def endpoint(pp, a0, key, chain: Const, digit: Const):
    node = hint_witness("wots")
    for step in unroll(digit, 15):
        node = f(pp, a0, key + const(chain * 2 ** 88 + step * 2 ** 120), node)
    return node, const(digit)


def xmss(pp, a0, key, bits: StackBuf(9), message):
    tips = StackBuf(38)
    tips[0] = pp
    tips[1] = a0
    tips[2] = key + const(1 * 2 ** 24)
    encoded = 0
    total = 1
    for chain in unroll(0, 35):
        digit = hint_witness("digit")
        assert log(digit) < 16
        tips[3 + chain], value = match(log(digit), range(0, 16), lambda d: endpoint(pp, a0, key, chain, d))
        if const(chain // 32 == 0):
            encoded += const(2 ** (8 * (chain // 2) + 4 * (1 - chain % 2))) * value
            total *= digit
        else:
            total *= digit ** (16 ** (34 - chain))
    assert encoded == message
    assert total == GEN ** 480
    ptr = addr(tips)
    node, unused = shake(ptr, 608)
    for level in unroll(0, 9):
        idx = 0
        for b in unroll(level + 1, 9):
            idx += const(2 ** (96 + 8 * (3 - (b - level - 1) // 8) + (b - level - 1) % 8)) * bits[b]
        sibling = hint_witness("ht_sibling")
        node = h(pp, a0, const(2 * 2 ** 24 + (level + 1) * 2 ** 88) + idx, node, sibling, bits[level])
    return node


def main():
    claim = StackBuf(CLAIMCELLS)
    hint_witness(claim, "claim")
    framing = StackBuf(128)
    hint_decompose_bits(framing, claim[2], 128)
    first = 0
    for b in unroll(0, 128):
        framing[b] = framing[b] * framing[b]
        first += const(2 ** b) * framing[b]
    for b in unroll(0, 8):
        assert framing[b] == 0
    for b in unroll(8, 16):
        assert framing[b] == const((CTXLEN // 2 ** (b - 8)) % 2)
    assert first == claim[2]
    if const(MPLEN % 16 != 0):
        last_bits = StackBuf(128)
        hint_decompose_bits(last_bits, claim[CLAIMCELLS - 1], 128)
        last = 0
        for b in unroll(0, 128):
            last_bits[b] = last_bits[b] * last_bits[b]
            last += const(2 ** b) * last_bits[b]
        assert last == claim[CLAIMCELLS - 1]
        for b in unroll(8 * (MPLEN % 16), 128):
            assert last_bits[b] == 0
    statement = StackBuf(2 + CLAIMCELLS)
    statement[0] = DOMAIN
    statement[1] = LENGTHS
    for i in unroll(0, CLAIMCELLS):
        statement[2 + i] = claim[i]
    public_digest = StackBuf(13)
    keccak_cells(statement, public_digest, len=64 + MPLEN)
    public = GEN ** 0
    public[1] = public_digest[0]
    public[GEN] = public_digest[1]
    hm = StackBuf(1 + CLAIMCELLS)
    rho = hint_witness("randomizer")
    hm[0] = rho
    for i in unroll(0, CLAIMCELLS):
        hm[1 + i] = claim[i]
    hm_ptr = addr(hm)
    d0, d1 = shake(hm_ptr, 48 + MPLEN)
    digest = StackBuf(256)
    hint_witness(digest, "digest_bits")
    v0 = 0
    v1 = 0
    for b in unroll(0, 128):
        digest[b] = digest[b] * digest[b]
        digest[128 + b] = digest[128 + b] * digest[128 + b]
        v0 += const(2 ** b) * digest[b]
        v1 += const(2 ** b) * digest[128 + b]
    assert d0 == v0
    assert d1 == v1
    indices = StackBuf(63)
    for b in unroll(0, 9):
        indices[b] = digest[8 * (29 - b // 8) + b % 8]
    for b in unroll(0, 54):
        indices[9 + b] = digest[8 * (27 - b // 8) + b % 8]
    tree = 0
    key = 0
    for b in unroll(0, 54):
        tree += const(2 ** (64 + 8 * (7 - b // 8) + b % 8)) * indices[9 + b]
    for b in unroll(0, 9):
        key += const(2 ** (32 + 8 * (3 - b // 8) + b % 8)) * indices[b]
    roots = StackBuf(17)
    roots[0] = claim[0]
    roots[1] = tree
    roots[2] = key + const(4 * 2 ** 24)
    for t in unroll(0, 14):
        fb = StackBuf(12)
        for b in unroll(0, 12):
            fb[b] = digest[8 * ((12 * t + 11 - b) // 8) + 7 - (12 * t + 11 - b) % 8]
        roots[3 + t] = fors_tree(claim[0], tree, key, fb, t)
    ptr = addr(roots)
    node, unused = shake(ptr, 272)
    for layer in unroll(0, 7):
        tree = const(layer * 2 ** 24)
        for b in unroll(0, 54 - 9 * layer):
            tree += const(2 ** (64 + 8 * (7 - b // 8) + b % 8)) * indices[9 * (layer + 1) + b]
        key = 0
        lb = StackBuf(9)
        for b in unroll(0, 9):
            lb[b] = indices[9 * layer + b]
            key += const(2 ** (32 + 8 * (3 - b // 8) + b % 8)) * lb[b]
        node = xmss(claim[0], tree, key, lb, node)
    assert node == claim[1]
    return

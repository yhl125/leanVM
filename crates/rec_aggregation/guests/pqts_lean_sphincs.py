from snark_lib import *

Y = 18446744073709551616
HI = 4294967296
TAG = 72057594037927936
HEIGHTS = [8, 8, 10]
DOMAIN = DOMAIN_PLACEHOLDER


@inline
def pair(node, sibling, bit):
    left = node + bit * (node + sibling)
    return left, left + node + sibling


def fors_tree(pp, index, bits: StackBuf(10), tree: Const):
    shifts = StackBuf(11)
    shifts[10] = 0
    for r in unroll(0, 10):
        shifts[9 - r] = bits[9 - r] + GEN * shifts[10 - r]
    secret = hint_witness("fors_secret")
    leaf = StackBuf(13)
    keccak([pp, index + const(15 * TAG + tree * HI) + const(64 * HI) * shifts[0]], [secret, 0], leaf, len=48)
    node = leaf[0]
    for level in unroll(0, 9):
        sibling = hint_witness("fors_sibling")
        left, right = pair(node, sibling, bits[level])
        parent = StackBuf(13)
        address = index + const(17 * TAG + (tree + 64 * (level + 1)) * HI) + const(1024 * HI) * shifts[level + 1]
        keccak([pp, address], [left, right], parent)
        node = parent[0]
    sibling = hint_witness("fors_sibling")
    left, right = pair(node, sibling, bits[9])
    return left, right


def counter():
    bits = StackBuf(32)
    hint_witness(bits, "counter")
    value = 0
    for bit in unroll(0, 32):
        bits[bit] = bits[bit] * bits[bit]
        value += const(2 ** bit) * bits[bit]
    return value


def endpoint(pp, at, chain: Const, digit: Const):
    node = hint_witness("wots")
    for step in unroll(digit, 3):
        state = StackBuf(13)
        keccak([pp, at + const((1 + 32 * step) * TAG + chain * HI)], [node, 0], state, len=48)
        node = state[0]
    return node, const(digit * 4 ** chain)


def hypertree(pp, base, bits: StackBuf(10), height: Const, encoding):
    shifts = StackBuf(11)
    shifts[10] = 0
    for r in unroll(0, 10):
        shifts[9 - r] = bits[9 - r] + GEN * shifts[10 - r]
    at = base + shifts[0]
    tips = StackBuf(66)
    tips[0] = pp
    tips[1] = at + const(2 * TAG)
    product = 1
    encoded = 0
    for chain in unroll(0, 64):
        digit = hint_witness("digit")
        assert log(digit) < 4
        tips[chain + 2], part = match(log(digit), range(0, 4), lambda d: endpoint(pp, at, chain, d))
        product *= digit
        encoded += part
    assert product == GEN ** 128
    assert encoded == encoding
    leaf = StackBuf(13)
    keccak_cells(tips, leaf)
    node = leaf[0]
    for level in unroll(0, height):
        sibling = hint_witness("ht_sibling")
        left, right = pair(node, sibling, bits[level])
        parent = StackBuf(13)
        keccak([pp, base + shifts[level + 1] + const(3 * TAG + (level + 1) * HI)], [left, right], parent)
        node = parent[0]
    return node


def main():
    claim = StackBuf(4)
    hint_witness(claim, "claim")
    statement = StackBuf(13)
    keccak_cells([DOMAIN, claim[0], claim[1], claim[2], claim[3]], statement)
    public = GEN ** 0
    public[1] = statement[0]
    public[GEN] = statement[1]
    pp = claim[1]
    rho = hint_witness("randomizer")
    digests = StackBuf(26)
    for call in unroll(0, 2):
        keccak([pp, const(12 * TAG + call * HI)], [claim[2], claim[3]], digests[13 * call:13 * call + 13], tail=[rho, 0, 0, 0], len=80)

    bits = StackBuf(512)
    hint_witness(bits, "digest_bits")
    for bit in unroll(0, 512):
        bits[bit] = bits[bit] * bits[bit]
    for part in unroll(0, 4):
        lo = 0
        hi = 0
        for bit in unroll(0, 64):
            lo += const(2 ** bit) * bits[128 * part + bit]
            hi += const(2 ** bit) * bits[128 * part + 64 + bit]
        digests[13 * (part // 2) + part % 2] = lo + Y * hi
    indices = StackBuf(27)
    indices[26] = 0
    for r in unroll(0, 26):
        indices[25 - r] = bits[25 - r] + GEN * indices[26 - r]

    fors = StackBuf(48)
    for tree in unroll(0, 24):
        leaf_bits = StackBuf(10)
        for bit in unroll(0, 10):
            leaf_bits[bit] = bits[26 + 10 * tree + bit]
        left, right = fors_tree(pp, indices[0], leaf_bits, tree)
        fors[2 * tree] = left
        fors[2 * tree + 1] = right

    for layer in unroll(0, 3):
        leaf_bits = StackBuf(10)
        leaf = 0
        for bit in unroll(0, HEIGHTS[layer]):
            leaf_bits[bit] = bits[8 * layer + bit]
            leaf += const(2 ** bit) * bits[8 * layer + bit]
        for bit in unroll(HEIGHTS[layer], 10):
            leaf_bits[bit] = 0
        base = Y * (layer + const(256) * indices[8 * layer + HEIGHTS[layer]])
        nonce = counter()
        encoding = StackBuf(13)
        if const(layer == 0):
            payload = StackBuf(51)
            payload[0] = pp
            payload[1] = base + leaf + const(4 * TAG)
            for word in unroll(0, 48):
                payload[word + 2] = fors[word]
            payload[50] = nonce
            keccak_cells(payload, encoding, len=804)
        else:
            keccak([pp, base + leaf + const(4 * TAG)], [node, nonce], encoding, len=52)
        node = hypertree(pp, base, leaf_bits, HEIGHTS[layer], encoding[0])
    assert node == claim[0]
    return

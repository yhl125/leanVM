# Appended to the existing recursive verifier and the checked PR152 raw verifier.
PR152_MAX_CLAIMS = PR152_MAX_CLAIMS_PLACEHOLDER


def main():
    meta = StackBuf(2)
    hint_witness(meta, "pr152_meta")
    n_g = meta[0]
    children_g = meta[1]
    assert log(n_g / GEN) < PR152_MAX_CLAIMS
    assert log(children_g) < 3
    seed = StackBuf(2)
    hint_witness(seed, "fs_seed")
    seed_0 = seed[0]
    seed_1 = seed[1]
    claims = HeapBuf(n_g ** 4)
    digest_0, digest_1 = claim_list_digest(claims, n_g)
    defer = HeapBuf(DEFER_STMT_CELLS)

    if children_g == 1:
        for item in mul_range(1, n_g):
            entry = claims * item ** 4
            claim = StackBuf(4)
            for word in unroll(0, 4):
                claim[word] = entry[GEN ** word]
            verify_pr152(claim)
        leaf_value = hint_witness("leaf_defer")
        for k in unroll(0, BYTECODE_VARS):
            defer[GEN ** k] = 0
        defer[GEN ** DEFER_STMT_BC_VALUE] = leaf_value
    else:
        assert children_g == GEN ** 2
        g_squares = exponent_tables()
        cover = HeapBuf(n_g)
        child_pi = HeapBuf(children_g ** 2)
        child_fresh = HeapBuf(children_g ** DEFER_SIZE)
        child_carried = HeapBuf(children_g ** DEFER_STMT_CELLS)
        written = HeapBuf(children_g * GEN)
        written[1] = 1
        for child in mul_range(1, children_g):
            child_n = hint_witness("pr152_child_count")
            assert log(child_n / GEN) < PR152_MAX_CLAIMS
            base = written[child]
            bigs, groups, rest = list_split(child_n)
            cd_0, cd_1 = child_claim_list_any(claims, cover, base, n_g, bigs, groups, rest)
            carried = child_carried * child ** DEFER_STMT_CELLS
            hint_witness(carried[0:DEFER_STMT_CELLS], "child_defer")
            pi_0, pi_1 = statement_digest(seed_0, seed_1, cd_0, cd_1, child_n, 0, 0, 0, carried)
            child_pi[child ** 2] = pi_0
            child_pi[child ** 2 * GEN] = pi_1
            verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, child_fresh * child ** DEFER_SIZE)
            written[child * GEN] = base * child_n
        assert written[children_g] == n_g
        aggregate_claims(children_g, child_pi, child_fresh, child_carried, defer)

    own_0, own_1 = statement_digest(seed_0, seed_1, digest_0, digest_1, n_g, 0, 0, 0, defer)
    public = GEN ** 0
    assert public[1] == own_0
    assert public[GEN] == own_1
    return

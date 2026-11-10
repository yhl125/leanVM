def main():
    count = hint_witness("batch_count")
    assert log(count / GEN) < BATCH_MAX_CLAIMS_PLACEHOLDER
    frame = StackBuf(2 + 2 * BATCH_MAX_CLAIMS_PLACEHOLDER)
    frame[0] = BATCH_DOMAIN_PLACEHOLDER
    frame[1] = count
    frame_ptr = addr(frame)
    entries = frame_ptr * GEN ** 2
    for item in mul_range(1, count):
        output = entries * item ** 2
        lo, hi = verify_slh()
        output[1] = lo
        output[GEN] = hi
    padding_base = entries * count ** 2
    for padding in mul_range(1, GEN ** BATCH_MAX_CLAIMS_PLACEHOLDER / count):
        output = padding_base * padding ** 2
        output[1] = 0
        output[GEN] = 0
    digest = StackBuf(13)
    keccak_cells(frame, digest)
    public = GEN ** 0
    public[1] = digest[0]
    public[GEN] = digest[1]
    return

// Pattern A: masked discriminant + sequential closed-form arithmetic. clang -O1 compiles this to `and $3,%eax; imul $100,%eax; add $5,%eax` in-place on the input register, which matches the strict Pattern A gate (Sset(R, R & M)). gcc -O1 uses a different SSA shape (Sset(t, p & M)) and wraps subsequent ops in casts, so Pattern A may not fire; the test tolerates this.
__attribute__((noinline))
int pattern_a_mask_and_scale(int x) {
    return (x & 3) * 100 + 5;
}

// Pattern B: bounded discriminant + cmov. clang -O1 emits cmov against -1; gcc -O1 may keep the if-else branch. Test tolerates either shape.
__attribute__((noinline))
int pattern_b_cmov_bounded(int x) {
    return (x >= 0 && x <= 7) ? (x * 10 + 5) : -1;
}

// Use argc as input so the optimizer cannot constant-fold the calls and elide the bodies.
int main(int argc, char **argv) {
    (void)argv;
    return pattern_a_mask_and_scale(argc) + pattern_b_cmov_bounded(argc);
}

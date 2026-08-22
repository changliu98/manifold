/* rotated_loops: loops whose dominance header is laid out AFTER the rest of
 * the body, so the header's in-loop arm is an explicit backward branch rather
 * than a fallthrough.  A `continue` recovered for such a loop must re-enter at
 * the header; binding it to the header's in-loop successor instead skips the
 * header test and turns the loop into an unconditional spin. */

volatile int sink;

/* gnulib xvasprintf's "%s%s..." prefix scan.  Entry lands on the '%' test,
 * which the compiler lays out after the 's' test and the increments. */
__attribute__((noinline))
int fmt_prefix_count(const char *f) {
    int n = 0;
    for (;;) {
        if (*f == '\0') return n;
        if (*f != '%') break;
        f++;
        if (*f != 's') break;
        f++;
        n++;
    }
    return -1;
}

/* Same rotation with an indexed access and a bounds test at the top. */
__attribute__((noinline))
int skip_escape_pairs(const unsigned char *p, int limit) {
    int i = 0;
    for (;;) {
        if (i >= limit) return i;
        if (p[i] != 0x1b) break;
        i++;
        if (p[i] != '[') break;
        i++;
    }
    return -i;
}

/* Rotated loop whose in-loop arm carries a side effect, so a skipped header
 * test is observable through the accumulator rather than only through hanging. */
__attribute__((noinline))
int run_length(const char *s, char c) {
    int n = 0;
    for (;;) {
        if (*s == '\0') break;
        if (*s != c) break;
        s++;
        n++;
        sink = n;
    }
    return n;
}

int main(void) {
    sink = fmt_prefix_count("%s%sx");
    sink += skip_escape_pairs((const unsigned char *)"\033[m", 3);
    sink += run_length("aaab", 'a');
    return sink;
}

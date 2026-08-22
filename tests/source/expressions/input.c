/* expressions: expression patterns from angr decompiler tests.
 * Covers: ternary recovery, magic division, modulo patterns,
 * compound assignments, chained comparisons.
 * Inspired by angr's test_decompiling_division3, test_decompiling_modulo_7ffffff,
 * test_automatic_ternary_creation, test_decompiling_simple_ctfbin_modulo. */

volatile int sink;

__attribute__((noinline))
int ternary_abs(int x) {
    return x > 0 ? x : -x;
}

__attribute__((noinline))
int ternary_max(int a, int b) {
    return a > b ? a : b;
}

__attribute__((noinline))
int ternary_clamp(int x, int lo, int hi) {
    int r = x < lo ? lo : x;
    return r > hi ? hi : r;
}

/* angr test_decompiling_division3: magic number division.
 * At -O1 gcc compiles n/3 to: imul + shift sequence.
 * Decompiler should recover "/ 3". */
__attribute__((noinline))
int divide_by_3(int n) {
    return n / 3;
}

__attribute__((noinline))
int divide_by_7(int n) {
    return n / 7;
}

__attribute__((noinline))
unsigned udivide_by_10(unsigned n) {
    return n / 10;
}

/* angr test_decompiling_simple_ctfbin_modulo: modulo recovery */
__attribute__((noinline))
int modulo_10(int n) {
    return n % 10;
}

__attribute__((noinline))
int modulo_and_div(int n) {
    int q = n / 5;
    int r = n % 5;
    sink = q;
    return r;
}

/* compound expressions: decompiler should recover clean expression trees */
__attribute__((noinline))
int compound_ops(int a, int b, int c) {
    a += b;
    a *= c;
    a -= b + c;
    sink = a;
    return a;
}

/* angr: chained boolean conditions */
__attribute__((noinline))
int range_check(int x, int lo, int hi) {
    if (x >= lo && x <= hi) {
        return 1;
    }
    return 0;
}

/* angr: cascading boolean AND */
__attribute__((noinline))
int multi_condition(int a, int b, int c, int d) {
    if (a > 0 && b > 0 && c > 0 && d > 0) {
        return a + b + c + d;
    }
    return 0;
}

/* expression with function call result used in condition
 * angr test_call_expr_folding_into_if_conditions */
__attribute__((noinline))
int call_in_condition(int x) {
    if (ternary_abs(x) > 10) {
        return 1;
    }
    return 0;
}

/* mixed arithmetic: tests expression tree reconstruction */
__attribute__((noinline))
int polynomial(int x) {
    return x * x * x - 3 * x * x + 2 * x - 1;
}

int main(void) {
    return ternary_abs(-5) + ternary_max(3, 7) + ternary_clamp(15, 0, 10)
         + divide_by_3(100) + divide_by_7(49) + udivide_by_10(123)
         + modulo_10(47) + modulo_and_div(23) + compound_ops(1, 2, 3)
         + range_check(5, 1, 10) + multi_condition(1, 2, 3, 4)
         + call_in_condition(-20) + polynomial(3);
}

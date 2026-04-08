/* var_basic: fundamental variable recovery patterns.
 * Tests basic def-use chains, single assignments, and simple variable lifetimes.
 */

volatile int sink;

__attribute__((noinline))
int test_single_var(int x) {
    int a = x + 1;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_two_vars(int x) {
    int a = x + 1;
    int b = x + 2;
    sink = a;
    return a + b;
}

__attribute__((noinline))
int test_three_vars(int x) {
    int a = x + 1;
    int b = x + 2;
    int c = x + 3;
    sink = a + b;
    return a + b + c;
}

__attribute__((noinline))
int test_chained_def(int x) {
    int a = x;
    int b = a + 1;
    int c = b + 1;
    int d = c + 1;
    sink = d;
    return d;
}

__attribute__((noinline))
int test_diamond_use(int x) {
    int a = x + 1;
    int r1 = a * 2;
    int r2 = a * 3;
    int r3 = a * 4;
    sink = r1 + r2;
    return r1 + r2 + r3;
}

__attribute__((noinline))
int test_redef_same_var(int x) {
    int a = x;
    sink = a;
    a = x + 1;
    sink = a;
    a = x + 2;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_unused_intermediate(int x) {
    int a = x + 1;
    int b = x + 2;  // b unused
    int c = x + 3;  // c unused
    sink = a;
    return a;
}

__attribute__((noinline))
int test_all_used(int x) {
    int a = x + 1;
    int b = x + 2;
    int c = x + 3;
    int d = a + b + c;
    sink = d;
    return d;
}

__attribute__((noinline))
int test_sequential_defs(int x, int y) {
    int a = x + y;
    int b = a + 1;
    int c = b + 1;
    sink = c;
    int d = c + 1;
    int e = d + 1;
    sink = e;
    return e;
}

__attribute__((noinline))
int test_interleaved_defs(int x, int y) {
    int a = x;
    int b = y;
    int c = a + 1;
    int d = b + 1;
    int e = c + d;
    sink = e;
    return e;
}

__attribute__((noinline))
int test_expression_temps(int x, int y, int z) {
    int r = (x + y) * (y + z) - (x * z);
    sink = r;
    return r;
}

__attribute__((noinline))
int test_nested_expression(int a, int b, int c, int d) {
    int r = ((a + b) * (c - d)) + ((a - b) * (c + d));
    sink = r;
    return r;
}

int main(void) {
    return test_single_var(1) + test_two_vars(2) + test_three_vars(3)
         + test_chained_def(4) + test_diamond_use(5) + test_redef_same_var(6)
         + test_unused_intermediate(7) + test_all_used(8)
         + test_sequential_defs(1, 2) + test_interleaved_defs(3, 4)
         + test_expression_temps(1, 2, 3) + test_nested_expression(1, 2, 3, 4);
}

/* var_copy_prop: copy propagation and dead store elimination tests.
 * Tests redundant copy removal and dead store detection.
 */

volatile int sink;

__attribute__((noinline))
int test_simple_copy(int x) {
    int a = x;
    int b = a;
    sink = b;
    return b;
}

__attribute__((noinline))
int test_chain_copy(int x) {
    int a = x;
    int b = a;
    int c = b;
    int d = c;
    sink = d;
    return d;
}

__attribute__((noinline))
int test_copy_with_use(int x) {
    int a = x;
    int b = a;
    sink = a;
    sink = b;
    return a + b;
}

__attribute__((noinline))
int test_dead_store_simple(int x) {
    int a = 1;
    a = 2;
    a = x;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_dead_store_chain(int x) {
    int a = 1;
    int b = a;
    a = 2;
    b = a;
    a = x;
    b = a;
    sink = b;
    return b;
}

__attribute__((noinline))
int test_partial_dead(int x) {
    int a = x;
    int b = a + 1;
    a = x + 2;
    sink = a + b;
    return a + b;
}

__attribute__((noinline))
int test_copy_across_branch(int x, int y) {
    int a = x;
    if (y > 0) {
        int b = a;
        sink = b;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_copy_to_multiple(int x) {
    int a = x;
    int b = a;
    int c = a;
    int d = a;
    sink = b + c + d;
    return b + c + d;
}

__attribute__((noinline))
int test_copy_from_param(int x, int y) {
    int a = x;
    int b = y;
    int c = a + b;
    sink = c;
    return c;
}

__attribute__((noinline))
int test_swap_pattern(int x, int y) {
    int t = x;
    int a = y;
    int b = t;
    sink = a;
    sink = b;
    return a + b;
}

__attribute__((noinline))
int test_copy_in_loop(int x, int n) {
    int a = x;
    for (int i = 0; i < n; i++) {
        int b = a;
        sink = b;
        a = a + 1;
    }
    return a;
}

__attribute__((noinline))
int test_redundant_reload(int x) {
    int a = x;
    sink = a;
    int b = a;
    sink = b;
    int c = a;
    sink = c;
    return a;
}

__attribute__((noinline))
int test_copy_then_modify(int x) {
    int a = x;
    int b = a;
    a = a + 1;
    sink = a;
    sink = b;
    return a + b;
}

__attribute__((noinline))
int test_dead_in_branch(int x) {
    int a = 1;
    if (x > 0) {
        a = 2;
    } else {
        a = 3;
    }
    sink = a;
    return a;
}

int main(void) {
    return test_simple_copy(1) + test_chain_copy(2) + test_copy_with_use(3)
         + test_dead_store_simple(4) + test_dead_store_chain(5)
         + test_partial_dead(6) + test_copy_across_branch(7, 1)
         + test_copy_to_multiple(8) + test_copy_from_param(9, 10)
         + test_swap_pattern(11, 12) + test_copy_in_loop(1, 5)
         + test_redundant_reload(13) + test_copy_then_modify(14)
         + test_dead_in_branch(15);
}

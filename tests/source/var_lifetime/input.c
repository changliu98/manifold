/* var_lifetime: variable lifetime and interference tests.
 * Tests overlapping lifetimes, reuse of registers, and non-interfering variables.
 */

volatile int sink;

__attribute__((noinline))
int test_non_overlapping(int x) {
    int a = x + 1;
    sink = a;
    int b = x + 2;
    sink = b;
    int c = x + 3;
    sink = c;
    return c;
}

__attribute__((noinline))
int test_overlapping_simple(int x) {
    int a = x + 1;
    int b = x + 2;
    sink = a + b;
    return a + b;
}

__attribute__((noinline))
int test_long_lifetime(int x) {
    int a = x + 1;
    int b = x + 2;
    int c = x + 3;
    int d = x + 4;
    sink = a;
    sink = b;
    sink = c;
    int r = a + b + c + d;
    sink = r;
    return r;
}

__attribute__((noinline))
int test_reuse_after_dead(int x) {
    int a = x + 1;
    sink = a;
    a = x + 2;
    sink = a;
    a = x + 3;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_interleaved_lifetimes(int x, int y) {
    int a = x;
    int b = y;
    sink = a;
    int c = a + 1;
    sink = b;
    int d = b + 1;
    sink = c;
    sink = d;
    return c + d;
}

__attribute__((noinline))
int test_nested_scopes(int x) {
    int a = x;
    sink = a;
    {
        int b = a + 1;
        sink = b;
        {
            int c = b + 1;
            sink = c;
        }
    }
    return a;
}

__attribute__((noinline))
int test_split_lifetime(int x) {
    int a = x;
    if (x > 0) {
        sink = a;
        a = a + 1;
    }
    sink = a;
    if (x > 5) {
        a = a + 2;
        sink = a;
    }
    return a;
}

__attribute__((noinline))
int test_parallel_vars(int x, int y) {
    int a = x + 1;
    int b = y + 1;
    int c = x + 2;
    int d = y + 2;
    int r1 = a + c;
    int r2 = b + d;
    sink = r1;
    sink = r2;
    return r1 + r2;
}

__attribute__((noinline))
int test_short_lived_temps(int x) {
    int t1 = x + 1;
    int r1 = t1 * 2;
    sink = r1;
    int t2 = x + 2;
    int r2 = t2 * 3;
    sink = r2;
    return r1 + r2;
}

__attribute__((noinline))
int test_interference_graph(int a, int b, int c, int d) {
    int w = a + b;
    int x = b + c;
    int y = c + d;
    int z = d + a;
    int r = w + x + y + z;
    sink = r;
    return r;
}

__attribute__((noinline))
int test_many_live_at_once(int a, int b, int c, int d, int e, int f) {
    int v1 = a + b;
    int v2 = b + c;
    int v3 = c + d;
    int v4 = d + e;
    int v5 = e + f;
    int v6 = f + a;
    int r = v1 + v2 + v3 + v4 + v5 + v6;
    sink = r;
    return r;
}

__attribute__((noinline))
int test_def_in_loop_body(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        int t = i * 2;
        sum += t;
    }
    return sum;
}

int main(void) {
    return test_non_overlapping(1) + test_overlapping_simple(2)
         + test_long_lifetime(3) + test_reuse_after_dead(4)
         + test_interleaved_lifetimes(5, 6) + test_nested_scopes(7)
         + test_split_lifetime(8) + test_parallel_vars(9, 10)
         + test_short_lived_temps(11) + test_interference_graph(1, 2, 3, 4)
         + test_many_live_at_once(1, 2, 3, 4, 5, 6) + test_def_in_loop_body(10);
}

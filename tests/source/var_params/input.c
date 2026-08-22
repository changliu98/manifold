/* var_params: function parameter recovery tests.
 * Tests recovery of function parameters across calling conventions.
 */

volatile int sink;

__attribute__((noinline))
int test_one_param(int a) {
    sink = a;
    return a + 1;
}

__attribute__((noinline))
int test_two_params(int a, int b) {
    sink = a + b;
    return a * b;
}

__attribute__((noinline))
int test_three_params(int a, int b, int c) {
    sink = a + b + c;
    return a * b + c;
}

__attribute__((noinline))
int test_four_params(int a, int b, int c, int d) {
    sink = a + b + c + d;
    return (a + b) * (c + d);
}

__attribute__((noinline))
int test_five_params(int a, int b, int c, int d, int e) {
    sink = a + b + c + d + e;
    return a * b + c * d + e;
}

__attribute__((noinline))
int test_six_params(int a, int b, int c, int d, int e, int f) {
    sink = a + b + c + d + e + f;
    return (a + b + c) * (d + e + f);
}

__attribute__((noinline))
int test_seven_params(int a, int b, int c, int d, int e, int f, int g) {
    sink = a + b + c + d + e + f + g;
    return a - b + c - d + e - f + g;
}

__attribute__((noinline))
int test_eight_params(int a, int b, int c, int d, int e, int f, int g, int h) {
    sink = a + b + c + d + e + f + g + h;
    return (a + b) * (c + d) + (e + f) * (g + h);
}

__attribute__((noinline))
long test_mixed_int_long(int a, long b, int c, long d) {
    long r = (long)a + b + (long)c + d;
    sink = (int)r;
    return r;
}

__attribute__((noinline))
int test_param_used_multiple(int a, int b) {
    int r1 = a + b;
    int r2 = a * b;
    int r3 = a - b;
    sink = r1 + r2 + r3;
    return r1 + r2 + r3;
}

__attribute__((noinline))
int test_param_in_conditional(int a, int b) {
    int r;
    if (a > b) {
        r = a - b;
    } else {
        r = b - a;
    }
    sink = r;
    return r;
}

__attribute__((noinline))
int test_param_in_loop(int a, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += a;
    }
    return sum;
}

__attribute__((noinline))
int test_param_modified(int a) {
    a = a + 1;
    sink = a;
    a = a * 2;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_param_passed_through(int a, int b) {
    return test_two_params(a, b) + test_two_params(b, a);
}

__attribute__((noinline))
int test_param_address_taken(int a) {
    int *p = &a;
    *p = *p + 1;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_variadic_style(int count, int a, int b, int c, int d) {
    int sum = 0;
    if (count >= 1) sum += a;
    if (count >= 2) sum += b;
    if (count >= 3) sum += c;
    if (count >= 4) sum += d;
    return sum;
}

__attribute__((noinline))
int test_param_reordering(int a, int b, int c, int d) {
    int t1 = d + a;
    int t2 = c + b;
    int t3 = b + c;
    int t4 = a + d;
    sink = t1 + t2 + t3 + t4;
    return t1 * t4 + t2 * t3;
}

__attribute__((noinline))
int test_unused_params(int a, int b, int c) {
    sink = a;
    return a + 1;
}

int main(void) {
    return test_one_param(1) + test_two_params(1, 2)
         + test_three_params(1, 2, 3) + test_four_params(1, 2, 3, 4)
         + test_five_params(1, 2, 3, 4, 5) + test_six_params(1, 2, 3, 4, 5, 6)
         + test_seven_params(1, 2, 3, 4, 5, 6, 7) + test_eight_params(1, 2, 3, 4, 5, 6, 7, 8)
         + (int)test_mixed_int_long(1, 2L, 3, 4L) + test_param_used_multiple(3, 4)
         + test_param_in_conditional(5, 3) + test_param_in_loop(2, 10)
         + test_param_modified(5) + test_param_passed_through(2, 3)
         + test_param_address_taken(10) + test_variadic_style(3, 1, 2, 3, 4)
         + test_param_reordering(1, 2, 3, 4) + test_unused_params(1, 2, 3);
}

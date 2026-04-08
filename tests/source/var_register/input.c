/* var_register: register allocation and pressure tests.
 * Tests variable recovery under high register pressure.
 */

volatile int sink;

__attribute__((noinline))
int test_all_caller_saved(int a, int b, int c, int d, int e, int f) {
    int r1 = a + b;
    int r2 = c + d;
    int r3 = e + f;
    sink = r1;
    sink = r2;
    sink = r3;
    return r1 + r2 + r3;
}

__attribute__((noinline))
int test_spill_to_stack(int a, int b, int c, int d, int e, int f) {
    int v1 = a + 1;
    int v2 = b + 2;
    int v3 = c + 3;
    int v4 = d + 4;
    int v5 = e + 5;
    int v6 = f + 6;
    int v7 = a + b;
    int v8 = c + d;
    int v9 = e + f;
    int v10 = v1 + v2;
    int v11 = v3 + v4;
    int v12 = v5 + v6;
    sink = v10;
    sink = v11;
    sink = v12;
    return v7 + v8 + v9 + v10 + v11 + v12;
}

__attribute__((noinline))
int test_caller_saved_across_call(int x) {
    int a = x + 1;
    int b = x + 2;
    int c = x + 3;
    sink = a + b + c;
    int d = a + b;
    int e = b + c;
    int f = a + c;
    sink = d + e + f;
    return d + e + f;
}

__attribute__((noinline))
int test_many_temps(int x, int y) {
    int t1 = x + y;
    int t2 = x - y;
    int t3 = x * y;
    int t4 = t1 + t2;
    int t5 = t2 + t3;
    int t6 = t1 + t3;
    int t7 = t4 + t5;
    int t8 = t5 + t6;
    int t9 = t6 + t4;
    sink = t7 + t8 + t9;
    return t7 + t8 + t9;
}

__attribute__((noinline))
int test_loop_with_many_vars(int n) {
    int sum1 = 0, sum2 = 0, sum3 = 0, sum4 = 0;
    for (int i = 0; i < n; i++) {
        sum1 += i;
        sum2 += i * 2;
        sum3 += i * 3;
        sum4 += i * 4;
    }
    sink = sum1 + sum2;
    return sum1 + sum2 + sum3 + sum4;
}

__attribute__((noinline))
int test_eight_params(int a, int b, int c, int d, int e, int f, int g, int h) {
    int r1 = a + b + c + d;
    int r2 = e + f + g + h;
    int r3 = a * e + b * f;
    int r4 = c * g + d * h;
    sink = r1 + r2;
    return r1 + r2 + r3 + r4;
}

__attribute__((noinline))
int test_nested_calls_pressure(int x) {
    int a = x + 1;
    int b = x + 2;
    int c = x + 3;
    int d = test_all_caller_saved(a, b, c, a, b, c);
    int e = test_all_caller_saved(b, c, a, b, c, a);
    sink = d + e;
    return d + e;
}

__attribute__((noinline))
int test_interleaved_computation(int a, int b, int c, int d) {
    int x1 = a + b;
    int y1 = c + d;
    int x2 = x1 * 2;
    int y2 = y1 * 2;
    int x3 = x2 + a;
    int y3 = y2 + c;
    int x4 = x3 * y1;
    int y4 = y3 * x1;
    sink = x4;
    sink = y4;
    return x4 + y4;
}

__attribute__((noinline))
int test_diamond_dag(int a, int b, int c) {
    int t1 = a + b;
    int t2 = b + c;
    int t3 = a + c;
    int r1 = t1 * t2;
    int r2 = t2 * t3;
    int r3 = t1 * t3;
    int final = r1 + r2 + r3;
    sink = final;
    return final;
}

__attribute__((noinline))
int test_long_chain_with_uses(int x) {
    int a = x;
    sink = a;
    int b = a + 1;
    sink = b;
    int c = b + 1;
    sink = c;
    int d = c + 1;
    sink = d;
    int e = d + 1;
    sink = e;
    int f = e + 1;
    sink = f;
    return a + b + c + d + e + f;
}

__attribute__((noinline))
int test_register_recycling(int x) {
    int a = x + 1;
    int r1 = a * 2;
    sink = r1;
    int b = x + 2;
    int r2 = b * 3;
    sink = r2;
    int c = x + 3;
    int r3 = c * 4;
    sink = r3;
    return r1 + r2 + r3;
}

int main(void) {
    return test_all_caller_saved(1, 2, 3, 4, 5, 6)
         + test_spill_to_stack(1, 2, 3, 4, 5, 6)
         + test_caller_saved_across_call(10)
         + test_many_temps(5, 3)
         + test_loop_with_many_vars(10)
         + test_eight_params(1, 2, 3, 4, 5, 6, 7, 8)
         + test_nested_calls_pressure(5)
         + test_interleaved_computation(1, 2, 3, 4)
         + test_diamond_dag(2, 3, 4)
         + test_long_chain_with_uses(1)
         + test_register_recycling(10);
}

/* abi_edges: ABI and call/return recovery edge cases.
 * Covers mixed integer return widths, stack-passed integer arguments,
 * out-parameters plus return values, indirect calls, void helpers, and
 * reusing a call result more than once.
 */

volatile int sink;
volatile int seed = 7;

__attribute__((noinline))
signed char ret_i8(int x) {
    return (signed char)(x - 130);
}

__attribute__((noinline))
unsigned short ret_u16(int x) {
    return (unsigned short)(x * 17 + 3);
}

__attribute__((noinline))
int ret_i32(int x) {
    return x * 3 - 1;
}

__attribute__((noinline))
long ret_i64(long x) {
    return x * 1000003L + 11L;
}

__attribute__((noinline))
int combine_return_widths(int x) {
    signed char a = ret_i8(x);
    unsigned short b = ret_u16(x + 1);
    int c = ret_i32(x + 2);
    long d = ret_i64((long)x + 3L);
    return (int)a + (int)b + c + (int)d;
}

__attribute__((noinline))
int more_than_six_args(int a, int b, int c, int d, int e, int f, int g, int h) {
    sink = g - h;
    return a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8;
}

__attribute__((noinline))
int call_with_stack_args(int x) {
    return more_than_six_args(x, x + 1, x + 2, x + 3, x + 4, x + 5, x + 6, x + 7);
}

__attribute__((noinline))
int outparam_and_return(int x, int y, int *sum_out, int *diff_out) {
    int sum = x + y;
    int diff = x - y;
    *sum_out = sum;
    *diff_out = diff;
    return sum ^ diff;
}

typedef int (*binary_op)(int, int);

__attribute__((noinline))
int add_edge(int a, int b) {
    return a + b;
}

__attribute__((noinline))
int xor_edge(int a, int b) {
    return a ^ b;
}

__attribute__((noinline))
int apply_selected(binary_op op, int x, int y) {
    return op(x, y);
}

__attribute__((noinline))
int select_and_call(int flag, int x, int y) {
    binary_op op;
    if (flag & 1) {
        op = add_edge;
    } else {
        op = xor_edge;
    }
    return apply_selected(op, x, y);
}

__attribute__((noinline))
void record_side_effect(int tag, int value) {
    sink = sink + tag + value;
}

__attribute__((noinline))
int void_helper_sequence(int x) {
    record_side_effect(1, x);
    record_side_effect(2, x + 1);
    return sink + x;
}

__attribute__((noinline))
int reuse_call_result(int x) {
    int v = ret_i32(x);
    int twice = v + v;
    sink = twice;
    return twice + v;
}

int main(void) {
    int a = seed;
    int sum = 0;
    int diff = 0;
    return combine_return_widths(a)
         + call_with_stack_args(a)
         + outparam_and_return(a + 10, a - 3, &sum, &diff)
         + select_and_call(a, sum, diff)
         + void_helper_sequence(a)
         + reuse_call_result(a);
}

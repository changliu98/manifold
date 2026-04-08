/* call_patterns: function call semantics.
 * Inspired by angr's call expression folding and ordering tests:
 * test_call_expr_folding_call_order, test_call_expr_folding_load_order,
 * test_call_expr_folding_store_order, test_decompiling_morton callbacks,
 * test_tail_calls, test_function_pointer_identification. */

#include <stdlib.h>

volatile int sink;
int global_state = 0;

__attribute__((noinline))
int pure_func(int x) {
    return x * 2 + 1;
}

__attribute__((noinline))
int side_effect_func(int x) {
    global_state += x;
    return global_state;
}

/* angr test_call_expr_folding_call_order:
 * calls with side effects must preserve ordering */
__attribute__((noinline))
int call_ordering(int x) {
    int a = side_effect_func(x);
    int b = side_effect_func(x + 1);
    return a + b;
}

/* angr: call result used in condition */
__attribute__((noinline))
int call_in_branch(int x) {
    int v = pure_func(x);
    if (v > 10) {
        sink = v;
        return v;
    }
    return 0;
}

/* angr test_decompiling_morton_my_message_callback:
 * multiple calls to same function with different args */
__attribute__((noinline))
int multiple_same_calls(int a, int b, int c) {
    int x = pure_func(a);
    int y = pure_func(b);
    int z = pure_func(c);
    return x + y + z;
}

/* angr test_tail_calls: tail call pattern */
__attribute__((noinline))
int tail_call_helper(int x, int acc) {
    if (x <= 0) return acc;
    return tail_call_helper(x - 1, acc + x);
}

__attribute__((noinline))
int tail_call_wrapper(int n) {
    return tail_call_helper(n, 0);
}

/* angr test_function_pointer_identification: function pointer dispatch */
typedef int (*op_func)(int, int);

__attribute__((noinline))
int add_func(int a, int b) { return a + b; }

__attribute__((noinline))
int sub_func(int a, int b) { return a - b; }

__attribute__((noinline))
int apply_op(op_func op, int x, int y) {
    return op(x, y);
}

__attribute__((noinline))
int dispatch_by_flag(int flag, int x, int y) {
    op_func op;
    if (flag) {
        op = add_func;
    } else {
        op = sub_func;
    }
    return apply_op(op, x, y);
}

/* chained function calls: deeply nested call tree */
__attribute__((noinline))
int chain_a(int x) { return pure_func(x) + 1; }

__attribute__((noinline))
int chain_b(int x) { return chain_a(x) + chain_a(x + 1); }

__attribute__((noinline))
int chain_c(int x) { return chain_b(x) * 2; }

/* angr: call with many arguments (stack args) */
__attribute__((noinline))
int many_args_callee(int a, int b, int c, int d, int e, int f, int g, int h) {
    return a + b + c + d + e + f + g + h;
}

__attribute__((noinline))
int many_args_caller(int x) {
    return many_args_callee(x, x+1, x+2, x+3, x+4, x+5, x+6, x+7);
}

/* callback pattern: pass function pointer and invoke */
__attribute__((noinline))
int with_callback(int *arr, int n, op_func cb) {
    int acc = 0;
    for (int i = 0; i < n; i++) {
        acc = cb(acc, arr[i]);
    }
    return acc;
}

int main(void) {
    int arr[] = {1, 2, 3, 4, 5};
    return call_ordering(1) + call_in_branch(10)
         + multiple_same_calls(1, 2, 3) + tail_call_wrapper(5)
         + dispatch_by_flag(1, 10, 3) + chain_c(2)
         + many_args_caller(1) + with_callback(arr, 5, add_func);
}

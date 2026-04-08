#include <stdio.h>
#include <stdlib.h>

volatile int sink;

__attribute__((noinline))
int test_identity(int x) {
    return x;
}

__attribute__((noinline))
int test_two_params(int a, int b) {
    return a + b;
}

__attribute__((noinline))
int test_three_params(int a, int b, int c) {
    return a * b + c;
}

__attribute__((noinline))
int test_def_use_chain(int x) {
    int a = x + 1;
    int b = a * 2;
    int c = b - 3;
    sink = c;
    return c;
}

__attribute__((noinline))
int test_cond_def(int x) {
    int r;
    if (x > 0) {
        r = x * 2;
        sink = 1;
    } else {
        r = -x;
        sink = 0;
    }
    return r;
}

__attribute__((noinline))
int test_loop_accumulator(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_call_arg_passing(int x) {
    int a = test_two_params(x, x + 1);
    int b = test_three_params(a, x, 10);
    return b;
}

__attribute__((noinline))
int test_multi_use(int x) {
    int a = x + 1;
    int b = a + a;
    int c = a * a;
    sink = b;
    return c;
}

__attribute__((noinline))
int test_loop_with_conditional_update(int *arr, int n) {
    int max = arr[0];
    for (int i = 1; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

__attribute__((noinline))
int test_chained_calls(int x) {
    return test_two_params(test_identity(x), test_identity(x + 1));
}

__attribute__((noinline))
int test_register_pressure(int a, int b, int c, int d, int e, int f) {
    int v1 = a + b;
    int v2 = b + c;
    int v3 = c + d;
    int v4 = d + e;
    int v5 = e + f;
    int v6 = f + a;
    int v7 = v1 * v2;
    int v8 = v3 * v4;
    int v9 = v5 * v6;
    int v10 = v7 - v8 + v9;
    sink = v10;
    return v10;
}

__attribute__((noinline))
int test_complex_phi(int x, int y, int z) {
    int r = 0;
    if (x > 0) {
        if (y > 0) {
            r = x + y;
        } else {
            r = x - y;
        }
    } else {
        for (int i = 0; i < z; i++) {
            r += i;
        }
    }
    return r;
}

__attribute__((noinline))
int test_aliasing_recovery(int x) {
    int a = x;
    int *p = &a;
    *p = a + 1;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_redundant_copies_and_dead_stores(int x) {
    int a = x;
    int b = a;
    int c = b;
    int d = c + 1;
    int e = d;
    int f = e;
    sink = f; // Only f (and thus d) is actually used
    return f;
}

__attribute__((noinline))
int test_partial_update(unsigned int x) {
    unsigned int a = x & 0xFF00FF00;
    unsigned int b = x & 0x00FF00FF;
    unsigned int c = a | (b << 1);
    sink = c;
    return c;
}

__attribute__((noinline))
int test_overlapping_lifetimes(int x, int y) {
    int a = x + 1;
    int b = y + 2;
    if (x > y) {
        int c = a + b;
        a = c * 2;
    } else {
        int d = a - b;
        b = d / 2;
    }
    return a + b;
}

struct Point {
    int x;
    int y;
};

__attribute__((noinline))
int test_stack_struct(int x, int y) {
    struct Point p;
    p.x = x;
    p.y = y;
    sink = p.x + p.y;
    return p.x * p.y;
}

__attribute__((noinline))
int test_sign_extension(signed char c) {
    int i = c;
    unsigned int u = (unsigned int)i;
    if (u > 0xFF) {
        return 1;
    }
    return 0;
}

__attribute__((noinline))
long test_large_consts(long x) {
    return x ^ 0xDEADBEEFCAFEBABE;
}

typedef int (*func_ptr)(int);
__attribute__((noinline))
int test_indirect_call(func_ptr f, int x) {
    return f(x) + 1;
}

__attribute__((noinline))
int test_tail_call(int x) {
    if (x > 0) return test_identity(x - 1);
    return 0;
}

__attribute__((noinline))
int test_switch_jump_table(int x) {
    switch (x) {
        case 1: return 10;
        case 2: return 20;
        case 3: return 30;
        case 4: return 40;
        case 5: return 50;
        case 6: return 60;
        case 7: return 70;
        case 8: return 80;
        case 9: return 90;
        default: return 0;
    }
}

__attribute__((noinline))
float test_float_math(float x, float y) {
    float a = x + y;
    float b = x - y;
    if (a > 0.0f) {
        return a * b;
    }
    return a / b;
}

__attribute__((noinline))
int test_pointer_arithmetic(int *arr, int len) {
    int sum = 0;
    int *end = arr + len;
    for (int *p = arr; p < end; p++) {
        sum += *p;
    }
    return sum;
}

int global_counter = 0;

__attribute__((noinline))
int test_global_var_update(int x) {
    global_counter += x;
    int a = global_counter;
    if (a > 100) {
        global_counter = 0;
    }
    return global_counter;
}

__attribute__((noinline))
int test_nested_loops_phi(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < i; j++) {
            sum += j;
        }
        sum -= i;
    }
    return sum;
}

__attribute__((noinline))
int test_div_mod(int a, int b) {
    if (b == 0) return 0;
    int q = a / b;
    int r = a % b;
    return q * r;
}

__attribute__((noinline))
int test_array_indexing(int *arr, int i, int j) {
    int x = arr[i + j];
    int y = arr[i - j];
    arr[i] = x + y;
    return arr[i];
}

__attribute__((noinline))
int test_bool_logic(int a, int b, int c) {
    if (a > 0 && (b < 10 || c == 5)) {
        return a + b;
    }
    return c;
}

/* Semantic equivalence harness: prints results for comparison */
int main(int argc, char **argv) {
    int mode = 0;
    if (argc > 1) mode = atoi(argv[1]);

    int arr[] = {3, 7, 1, 9, 2};

    switch (mode) {
        case 0: printf("%d\n", test_identity(42)); break;
        case 1: printf("%d\n", test_two_params(3, 4)); break;
        case 2: printf("%d\n", test_three_params(2, 3, 4)); break;
        case 3: printf("%d\n", test_def_use_chain(5)); break;
        case 4: printf("%d\n", test_cond_def(7)); break;
        case 5: printf("%d\n", test_cond_def(-3)); break;
        case 6: printf("%d\n", test_loop_accumulator(10)); break;
        case 7: printf("%d\n", test_call_arg_passing(5)); break;
        case 8: printf("%d\n", test_multi_use(4)); break;
        case 9: printf("%d\n", test_loop_with_conditional_update(arr, 5)); break;
        case 10: printf("%d\n", test_chained_calls(3)); break;
        case 11: printf("%d\n", test_register_pressure(1, 2, 3, 4, 5, 6)); break;
        case 12: printf("%d\n", test_complex_phi(1, 1, 5)); break;
        case 13: printf("%d\n", test_complex_phi(-1, 0, 5)); break;
        case 14: printf("%d\n", test_aliasing_recovery(10)); break;
        case 15: printf("%d\n", test_redundant_copies_and_dead_stores(5)); break;
        case 16: printf("%d\n", test_partial_update(0x12345678)); break;
        case 17: printf("%d\n", test_overlapping_lifetimes(5, 3)); break;
        case 18: printf("%d\n", test_stack_struct(3, 4)); break;
        case 19: printf("%d\n", test_sign_extension(-1)); break;
        case 20: printf("%ld\n", test_large_consts(0)); break;
        case 21: printf("%d\n", test_indirect_call(test_identity, 5)); break;
        case 22: printf("%d\n", test_tail_call(5)); break;
        case 23: printf("%d\n", test_switch_jump_table(3)); break;
        case 24: printf("%f\n", test_float_math(3.0f, 2.0f)); break;
        case 25: printf("%d\n", test_pointer_arithmetic(arr, 5)); break;
        case 26: printf("%d\n", test_global_var_update(10)); break;
        case 27: printf("%d\n", test_nested_loops_phi(5)); break;
        case 28: printf("%d\n", test_div_mod(10, 3)); break;
        case 29: printf("%d\n", test_array_indexing(arr, 2, 1)); break;
        case 30: printf("%d\n", test_bool_logic(5, 12, 5)); break;
        default: break;
    }
    return 0;
}

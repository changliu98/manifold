/* var_return: return value recovery tests.
 * Tests recovery of return values and their uses.
 */

volatile int sink;

__attribute__((noinline))
int test_return_const(void) {
    return 42;
}

__attribute__((noinline))
int test_return_param(int x) {
    return x;
}

__attribute__((noinline))
int test_return_computed(int x, int y) {
    return x + y;
}

__attribute__((noinline))
int test_return_conditional(int x) {
    if (x > 0) {
        return 1;
    } else {
        return -1;
    }
}

__attribute__((noinline))
int test_return_from_loop(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_return_chain(int x) {
    int a = x + 1;
    int b = a + 1;
    int c = b + 1;
    return c;
}

__attribute__((noinline))
int test_return_used(int x) {
    int a = test_return_param(x);
    int b = a + 1;
    sink = b;
    return b;
}

__attribute__((noinline))
int test_return_in_expression(int x, int y) {
    return test_return_param(x) + test_return_param(y);
}

__attribute__((noinline))
int test_return_nested_calls(int x) {
    return test_return_computed(test_return_param(x), test_return_const());
}

__attribute__((noinline))
int test_return_early(int x) {
    if (x < 0) return -1;
    if (x == 0) return 0;
    return x;
}

__attribute__((noinline))
int test_return_from_switch(int x) {
    switch (x) {
        case 0: return 10;
        case 1: return 20;
        case 2: return 30;
        default: return 0;
    }
}

__attribute__((noinline))
int test_return_stored_then_returned(int x) {
    int result = x * 2;
    sink = result;
    return result;
}

__attribute__((noinline))
int test_return_modified_before_return(int x) {
    int r = x;
    r = r + 1;
    r = r * 2;
    return r;
}

__attribute__((noinline))
int test_return_from_phi(int x, int y) {
    int r;
    if (x > y) {
        r = x - y;
    } else {
        r = y - x;
    }
    return r;
}

__attribute__((noinline))
int test_return_complex_expression(int a, int b, int c) {
    return (a + b) * (b + c) - (a * c);
}

__attribute__((noinline))
int test_return_ignored(int x) {
    test_return_param(x);
    return 0;
}

__attribute__((noinline))
int test_return_multiple_paths(int x, int y, int z) {
    if (x > 0) {
        if (y > 0) {
            return x + y;
        }
        return x;
    }
    if (z > 0) {
        return z;
    }
    return -1;
}

__attribute__((noinline))
long test_return_long(long x) {
    return x * 2;
}

__attribute__((noinline))
int test_return_truncated(long x) {
    return (int)(x & 0xFFFFFFFF);
}

__attribute__((noinline))
int helper_return_val(int x) {
    return x + 100;
}

__attribute__((noinline))
int test_return_through_helper(int x) {
    int a = helper_return_val(x);
    int b = helper_return_val(a);
    return b;
}

int main(void) {
    return test_return_const() + test_return_param(5)
         + test_return_computed(3, 4) + test_return_conditional(5)
         + test_return_from_loop(10) + test_return_chain(1)
         + test_return_used(5) + test_return_in_expression(3, 4)
         + test_return_nested_calls(5) + test_return_early(5)
         + test_return_from_switch(1) + test_return_stored_then_returned(5)
         + test_return_modified_before_return(5) + test_return_from_phi(5, 3)
         + test_return_complex_expression(1, 2, 3) + test_return_ignored(5)
         + test_return_multiple_paths(1, 2, 3) + (int)test_return_long(5L)
         + test_return_truncated(1000000L) + test_return_through_helper(5);
}

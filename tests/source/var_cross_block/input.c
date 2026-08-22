/* var_cross_block: cross-block variable recovery tests.
 * Tests variables that live across basic block boundaries.
 */

volatile int sink;

__attribute__((noinline))
int test_def_in_pred(int x) {
    int a = x + 1;
    if (x > 0) {
        sink = a;
    }
    return a;
}

__attribute__((noinline))
int test_use_in_succ(int x) {
    int a;
    if (x > 0) {
        a = x * 2;
    } else {
        a = x * 3;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_live_across_loop(int n) {
    int a = 10;
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += a;
    }
    return sum + a;
}

__attribute__((noinline))
int test_multiple_preds(int x, int y) {
    int a;
    if (x > 0) {
        a = 1;
    } else if (y > 0) {
        a = 2;
    } else {
        a = 3;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_multiple_succs(int x) {
    int a = x + 1;
    if (x > 10) {
        sink = a;
        return a + 1;
    } else if (x > 5) {
        sink = a;
        return a + 2;
    } else {
        sink = a;
        return a + 3;
    }
}

__attribute__((noinline))
int test_diamond_cfg(int x) {
    int a = 0;
    if (x > 0) {
        a = x + 1;
    } else {
        a = x - 1;
    }
    int b = a * 2;
    sink = b;
    return b;
}

__attribute__((noinline))
int test_loop_back_edge(int n) {
    int sum = 0;
    int prev = 0;
    for (int i = 0; i < n; i++) {
        int tmp = sum;
        sum = prev + i;
        prev = tmp;
    }
    return sum;
}

__attribute__((noinline))
int test_nested_cfg(int x, int y) {
    int a = 1;
    if (x > 0) {
        if (y > 0) {
            a = a + x;
        } else {
            a = a + y;
        }
        a = a * 2;
    } else {
        a = a - 1;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_early_return(int x) {
    int a = x + 1;
    if (x < 0) {
        return -1;
    }
    int b = a + 1;
    if (x > 100) {
        return b;
    }
    return a + b;
}

__attribute__((noinline))
int test_switch_cfg(int x) {
    int a = 0;
    switch (x) {
        case 1: a = 10; break;
        case 2: a = 20; break;
        case 3: a = 30; break;
        default: a = -1;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_break_in_loop(int *arr, int n, int target) {
    int found_idx = -1;
    for (int i = 0; i < n; i++) {
        if (arr[i] == target) {
            found_idx = i;
            break;
        }
    }
    return found_idx;
}

__attribute__((noinline))
int test_complex_cfg(int a, int b, int c) {
    int result = 0;
    if (a > 0) {
        result = a;
        if (b > 0) {
            result += b;
        }
    } else {
        result = -a;
        if (c > 0) {
            result += c;
        } else {
            result -= c;
        }
    }
    int final = result * 2;
    sink = final;
    return final;
}

__attribute__((noinline))
int test_critical_edge(int x, int y) {
    int a = x;
    int b = y;
    if (x > 0) {
        a = a + 1;
        if (y > 0) {
            b = b + 1;
        }
    }
    return a + b;
}

__attribute__((noinline))
int test_backedge_live_var(int n) {
    int a = 1;
    int b = 1;
    while (n > 0) {
        int tmp = a;
        a = a + b;
        b = tmp;
        n--;
    }
    return a;
}

int main(void) {
    int arr[] = {1, 5, 3, 9, 7};
    return test_def_in_pred(5) + test_use_in_succ(5)
         + test_live_across_loop(10) + test_multiple_preds(1, 2)
         + test_multiple_succs(7) + test_diamond_cfg(5)
         + test_loop_back_edge(10) + test_nested_cfg(1, 2)
         + test_early_return(50) + test_switch_cfg(2)
         + test_break_in_loop(arr, 5, 3) + test_complex_cfg(1, 2, 3)
         + test_critical_edge(1, 2) + test_backedge_live_var(10);
}

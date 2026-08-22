/* var_loop: loop induction variable and accumulator tests.
 * Tests variable recovery in loop constructs.
 */

volatile int sink;

__attribute__((noinline))
int test_simple_for(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_while_counter(int n) {
    int count = 0;
    int i = 0;
    while (i < n) {
        count++;
        i++;
    }
    return count;
}

__attribute__((noinline))
int test_do_while_decrement(int n) {
    int i = n;
    int result = 0;
    do {
        result += i;
        i--;
    } while (i > 0);
    return result;
}

__attribute__((noinline))
int test_nested_loop_counters(int n, int m) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m; j++) {
            sum += i * j;
        }
    }
    return sum;
}

__attribute__((noinline))
int test_multiple_accumulators(int n) {
    int sum1 = 0, sum2 = 0;
    for (int i = 0; i < n; i++) {
        sum1 += i;
        sum2 += i * 2;
    }
    return sum1 + sum2;
}

__attribute__((noinline))
int test_loop_carried_dependency(int n) {
    int prev = 0;
    int curr = 1;
    for (int i = 0; i < n; i++) {
        int next = prev + curr;
        prev = curr;
        curr = next;
    }
    return curr;
}

__attribute__((noinline))
int test_stride_two(int n) {
    int sum = 0;
    for (int i = 0; i < n; i += 2) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_countdown(int n) {
    int sum = 0;
    for (int i = n; i > 0; i--) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_early_break(int *arr, int n, int target) {
    int idx = -1;
    for (int i = 0; i < n; i++) {
        if (arr[i] == target) {
            idx = i;
            break;
        }
    }
    return idx;
}

__attribute__((noinline))
int test_continue_skip(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) continue;
        sum += i;
    }
    return sum;
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
int test_multiple_induction_vars(int n) {
    int sum = 0;
    for (int i = 0, j = n; i < j; i++, j--) {
        sum += i + j;
    }
    return sum;
}

__attribute__((noinline))
int test_loop_invariant_motion(int n, int c) {
    int sum = 0;
    int invariant = c * 2;
    for (int i = 0; i < n; i++) {
        sum += invariant + i;
    }
    return sum;
}

__attribute__((noinline))
int test_reduction(int *arr, int n) {
    int product = 1;
    for (int i = 0; i < n; i++) {
        product *= arr[i];
    }
    return product;
}

__attribute__((noinline))
int test_inner_loop_var_reuse(int n) {
    int total = 0;
    for (int i = 0; i < n; i++) {
        int inner_sum = 0;
        for (int j = 0; j <= i; j++) {
            inner_sum += j;
        }
        total += inner_sum;
    }
    return total;
}

__attribute__((noinline))
int test_triple_nested(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            for (int k = 0; k < n; k++) {
                sum += i + j + k;
            }
        }
    }
    return sum;
}

int main(void) {
    int arr[] = {3, 1, 4, 1, 5, 9, 2, 6};
    return test_simple_for(10) + test_while_counter(10)
         + test_do_while_decrement(5) + test_nested_loop_counters(3, 4)
         + test_multiple_accumulators(10) + test_loop_carried_dependency(10)
         + test_stride_two(20) + test_countdown(10)
         + test_early_break(arr, 8, 5) + test_continue_skip(10)
         + test_loop_with_conditional_update(arr, 8)
         + test_multiple_induction_vars(10) + test_loop_invariant_motion(10, 5)
         + test_reduction(arr, 5) + test_inner_loop_var_reuse(5)
         + test_triple_nested(3);
}

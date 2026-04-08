/* loops_advanced: advanced loop patterns.
 * Inspired by angr's test_decompiling_dirname_last_component_missing_loop
 * (multiple for-loop recovery), test_single_instruction_loop,
 * test_simple_strcpy (do-while post-increment), and
 * test_decompiling_du_humblock_missing_conditions (break without goto). */

volatile int sink;

/* angr test_decompiling_dirname_last_component_missing_loop:
 * multiple sequential loops in one function */
__attribute__((noinline))
int multiple_sequential_loops(int *arr, int n) {
    int sum = 0;
    /* loop 1: accumulate */
    for (int i = 0; i < n; i++) {
        sum += arr[i];
    }
    /* loop 2: find max */
    int max = arr[0];
    for (int i = 1; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    /* loop 3: count positives */
    int pos = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] > 0) {
            pos++;
        }
    }
    return sum + max + pos;
}

/* sentinel loop: while(*p) p++ pattern, common in string processing */
__attribute__((noinline))
int sentinel_loop(const char *s) {
    int count = 0;
    while (*s) {
        if (*s >= 'a' && *s <= 'z') {
            count++;
        }
        s++;
    }
    return count;
}

/* do-while with break: angr test_decompiling_du_humblock_missing_conditions */
__attribute__((noinline))
int do_while_with_break(int *arr, int n) {
    int i = 0;
    int sum = 0;
    do {
        sum += arr[i];
        if (arr[i] == 0) {
            break;
        }
        i++;
    } while (i < n);
    return sum;
}

/* countdown loop */
__attribute__((noinline))
int countdown(int n) {
    int acc = 0;
    while (n > 0) {
        acc += n;
        n--;
    }
    return acc;
}

/* loop with multiple exits: break + return
 * angr test_decompiling_du_humblock: break without goto */
__attribute__((noinline))
int loop_multi_exit(int *arr, int n, int target) {
    for (int i = 0; i < n; i++) {
        if (arr[i] == target) {
            return i;
        }
        if (arr[i] < 0) {
            break;
        }
    }
    return -1;
}

/* nested loop with accumulator: inner loop depends on outer variable */
__attribute__((noinline))
int triangle_sum(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) {
        for (int j = 1; j <= i; j++) {
            sum += j;
        }
    }
    return sum;
}

/* loop with function call inside: call should not be hoisted
 * angr test_call_expr_folding_call_loop */
__attribute__((noinline))
int loop_with_call(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        int val = countdown(arr[i]);
        sum += val;
    }
    return sum;
}

/* while-true with break: tests infinite loop + break structuring */
__attribute__((noinline))
int while_true_pattern(int start) {
    int x = start;
    while (1) {
        x = x * 3 + 1;
        if (x > 10000) {
            break;
        }
        if (x % 2 == 0) {
            x = x / 2;
        }
    }
    return x;
}

int main(void) {
    int arr[] = {3, 7, -1, 9, 0, 2};
    return multiple_sequential_loops(arr, 4)
         + sentinel_loop("Hello World 123")
         + do_while_with_break(arr, 6)
         + countdown(10) + loop_multi_exit(arr, 6, 9)
         + triangle_sum(5) + loop_with_call(arr, 3)
         + while_true_pattern(1);
}

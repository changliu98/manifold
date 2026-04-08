volatile int sink;

__attribute__((noinline))
int test_if_in_while(int n) {
    int sum = 0;
    while (n > 0) {
        if (n % 2 == 0) {
            sum += n;
        }
        n--;
    }
    return sum;
}

__attribute__((noinline))
int test_while_in_while(int rows, int cols) {
    int total = 0;
    int r = 0;
    while (r < rows) {
        int c = 0;
        while (c < cols) {
            total += r * cols + c;
            c++;
        }
        r++;
    }
    return total;
}

__attribute__((noinline))
int test_for_with_break(int *arr, int n, int target) {
    for (int i = 0; i < n; i++) {
        if (arr[i] == target) {
            sink = i;
            return i;
        }
    }
    return -1;
}

__attribute__((noinline))
int test_for_with_continue(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] < 0) continue;
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
int test_complex_condition(int a, int b, int c) {
    if (a > 0 && b > 0) {
        sink = 1;
        return a + b;
    }
    if (a < 0 || c < 0) {
        sink = 2;
        return c;
    }
    sink = 3;
    return 0;
}

__attribute__((noinline))
int test_loop_with_two_exits(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += arr[i];
        if (sum > 100) {
            sink = sum;
            return sum;
        }
        if (arr[i] == 0) {
            break;
        }
    }
    return sum;
}

int main(void) {
    int arr[] = {3, -1, 4, 0, 5, -2, 7};
    return test_if_in_while(10)
         + test_while_in_while(3, 4)
         + test_for_with_break(arr, 7, 4)
         + test_for_with_continue(arr, 7)
         + test_complex_condition(1, 2, 3)
         + test_loop_with_two_exits(arr, 7);
}

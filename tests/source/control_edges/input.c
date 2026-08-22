volatile int sink;

__attribute__((noinline))
int multi_continue_loop(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        int v = arr[i];
        if (v < 0) {
            continue;
        }
        if ((v & 1) == 0) {
            sum += v / 2;
            continue;
        }
        if (v == 13) {
            continue;
        }
        sum += v;
    }
    sink = sum;
    return sum;
}

__attribute__((noinline))
int nested_loop_early_return(int *arr, int rows, int cols, int target) {
    int seen = 0;
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int v = arr[r * cols + c];
            if (v == target) {
                return seen + r + c;
            }
            if (v < 0) {
                return -seen - 1;
            }
            seen += v & 3;
        }
    }
    return seen;
}

__attribute__((noinline))
int switch_negative_default_loop(int *arr, int n) {
    int score = 0;
    for (int i = 0; i < n; i++) {
        switch (arr[i]) {
            case -3:
                score -= 30;
                break;
            case -1:
                score -= 10;
                break;
            case 0:
                score += 1;
                break;
            case 2:
                score += 20;
                break;
            default:
                score += 7;
                break;
        }
    }
    return score;
}

__attribute__((noinline))
int post_test_guard_loop(int *arr, int n) {
    int i = 0;
    int total = 0;
    if (n <= 0) {
        return 0;
    }
    do {
        int v = arr[i++];
        if (v == 0) {
            break;
        }
        total += v;
    } while (i < n && total < 100);
    return total;
}

__attribute__((noinline))
int if_switch_composition(int mode, int value) {
    int out = 0;
    if (mode < 0) {
        switch (value) {
            case -2:
                out = -20;
                break;
            case -1:
                out = -10;
                break;
            default:
                out = -1;
                break;
        }
    } else if (mode == 0) {
        if (value == 0) {
            out = 100;
        } else {
            out = value + 1;
        }
    } else {
        switch (value & 3) {
            case 0:
                out = mode;
                break;
            case 1:
                out = mode + value;
                break;
            default:
                out = mode - value;
                break;
        }
    }
    return out;
}

int main(void) {
    int arr[] = {4, -1, 13, 7, 0, 2, -3, 9};
    return multi_continue_loop(arr, 8)
         + nested_loop_early_return(arr, 2, 4, 9)
         + switch_negative_default_loop(arr, 8)
         + post_test_guard_loop(arr, 8)
         + if_switch_composition(-1, -2);
}

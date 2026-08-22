volatile int sink;

__attribute__((noinline))
int if_else_basic(int x) {
    if (x > 0) {
        return x + 1;
    } else {
        return x - 1;
    }
}

__attribute__((noinline))
int if_else_ladder(int x) {
    if (x < 0) {
        return -1;
    } else if (x == 0) {
        return 0;
    } else if (x == 1) {
        return 1;
    } else if (x < 10) {
        return 2;
    } else {
        return 3;
    }
}

__attribute__((noinline))
int nested_if_else(int a, int b, int c) {
    int r = 0;
    if (a > 0) {
        if (b > 0) {
            r = a + b;
        } else {
            r = a - b;
        }
    } else {
        if (c > 0) {
            r = c;
        } else {
            r = -c;
        }
    }
    sink = r;
    return r;
}

__attribute__((noinline))
int guard_chain(int x) {
    if (x < 0) {
        return -1;
    }
    if (x == 0) {
        return 0;
    }
    if (x > 100) {
        return 100;
    }
    if ((x & 1) == 0) {
        return x / 2;
    }
    return x;
}

__attribute__((noinline))
int while_counter(int n) {
    int sum = 0;
    while (n > 0) {
        sum += n;
        n--;
    }
    return sum;
}

__attribute__((noinline))
int while_break_continue(int n) {
    int sum = 0;
    while (n > 0) {
        n--;
        if ((n & 1) == 0) {
            continue;
        }
        if (n == 3) {
            break;
        }
        sum += n;
    }
    return sum;
}

__attribute__((noinline))
int do_while_increment(int n) {
    int v = 0;
    do {
        v += 2;
        n--;
    } while (n > 0);
    return v;
}

__attribute__((noinline))
int for_accumulate(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int for_break_on_target(int *arr, int n, int target) {
    for (int i = 0; i < n; i++) {
        if (arr[i] == target) {
            return i;
        }
    }
    return -1;
}

__attribute__((noinline))
int for_continue_skip_negative(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] < 0) {
            continue;
        }
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
int nested_for_sum(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= i; j++) {
            sum += i + j;
        }
    }
    return sum;
}

__attribute__((noinline))
int mixed_loop_nesting(int n) {
    int sum = 0;
    int i = 0;
    while (i < n) {
        for (int j = 0; j < 2; j++) {
            sum += i + j;
        }
        i++;
    }
    return sum;
}

__attribute__((noinline))
int infinite_loop_break(int start) {
    int x = start;
    while (1) {
        x = x * 2 + 1;
        if (x > 1000) {
            break;
        }
    }
    return x;
}

__attribute__((noinline))
int loop_multi_exit(int *arr, int n, int stop) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] == stop) {
            return sum;
        }
        if (arr[i] < 0) {
            break;
        }
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
int switch_dense(int x) {
    switch (x) {
        case 0: return 10;
        case 1: return 20;
        case 2: return 30;
        case 3: return 40;
        case 4: return 50;
        case 5: return 60;
        case 6: return 70;
        case 7: return 80;
        default: return -1;
    }
}

__attribute__((noinline))
int switch_sparse(int x) {
    switch (x) {
        case 3: return 11;
        case 11: return 22;
        case 29: return 33;
        case 47: return 44;
        case 101: return 55;
        default: return 0;
    }
}

__attribute__((noinline))
int switch_fallthrough(int x) {
    int acc = 0;
    switch (x & 7) {
        case 0:
            acc += 1;
        case 1:
            acc += 10;
            break;
        case 2:
        case 3:
            acc += 100;
            break;
        case 4:
            acc += 1000;
        case 5:
            acc += 10000;
            break;
        default:
            acc = -1;
            break;
    }
    sink = acc;
    return acc;
}

__attribute__((noinline))
int switch_in_loop(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        switch (arr[i] & 3) {
            case 0: sum += 1; break;
            case 1: sum += 10; break;
            case 2: sum += 100; break;
            case 3: sum -= 1; break;
        }
    }
    return sum;
}

__attribute__((noinline))
int switch_under_if(int x, int y) {
    if (x > 0) {
        switch (y) {
            case 0: return 1;
            case 1: return 2;
            default: return 3;
        }
    }
    if (x == 0) {
        return 4;
    }
    return -1;
}

__attribute__((noinline))
int if_inside_switch(int x, int y) {
    switch (x & 3) {
        case 0:
            if (y > 0) {
                return 10;
            } else {
                return 11;
            }
        case 1:
            if (y < 0) {
                return 20;
            }
            return 21;
        case 2:
            return 30;
        default:
            return 40;
    }
}

__attribute__((noinline))
int complex_control_mesh(int *arr, int n) {
    int acc = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] == 0) {
            continue;
        }
        if (arr[i] < 0) {
            break;
        }
        switch (arr[i] & 3) {
            case 0:
                acc += arr[i];
                break;
            case 1:
                acc += 2 * arr[i];
                break;
            case 2:
                acc -= arr[i];
                break;
            default:
                acc += 1;
                break;
        }
        if (acc > 200) {
            return acc;
        }
    }
    return acc;
}

int main(void) {
    int arr[] = {3, -1, 4, 0, 5, 9, 2, 6};
    return if_else_basic(3)
         + if_else_ladder(2)
         + nested_if_else(4, -1, 5)
         + guard_chain(8)
         + while_counter(7)
         + while_break_continue(12)
         + do_while_increment(4)
         + for_accumulate(6)
         + for_break_on_target(arr, 8, 9)
         + for_continue_skip_negative(arr, 8)
         + nested_for_sum(5)
         + mixed_loop_nesting(4)
         + infinite_loop_break(1)
         + loop_multi_exit(arr, 8, 9)
         + switch_dense(3)
         + switch_sparse(47)
         + switch_fallthrough(4)
         + switch_in_loop(arr, 8)
         + switch_under_if(1, 1)
         + if_inside_switch(1, -1)
         + complex_control_mesh(arr, 8);
}

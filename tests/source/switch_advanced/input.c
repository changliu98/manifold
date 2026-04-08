/* switch_advanced: comprehensive switch statement patterns.
 * Inspired by angr's switch0/1/2 decompiler tests that validate
 * case/default/break recovery from jump tables. */

volatile int sink;

__attribute__((noinline))
int switch_with_default(int x) {
    int r;
    switch (x) {
        case 0: r = 100; break;
        case 1: r = 200; break;
        case 2: r = 300; break;
        case 3: r = 400; break;
        case 4: r = 500; break;
        case 5: r = 600; break;
        case 6: r = 700; break;
        case 7: r = 800; break;
        default: r = -1; break;
    }
    sink = r;
    return r;
}

__attribute__((noinline))
int switch_no_default(int x) {
    int r = 0;
    switch (x & 3) {
        case 0: r = 10; break;
        case 1: r = 20; break;
        case 2: r = 30; break;
        case 3: r = 40; break;
    }
    return r;
}

__attribute__((noinline))
int switch_sparse(int x) {
    switch (x) {
        case 1:   return 11;
        case 10:  return 22;
        case 100: return 33;
        case 200: return 44;
        case 500: return 55;
        default:  return 0;
    }
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
int switch_nested(int x, int y) {
    int r = 0;
    switch (x & 3) {
        case 0:
            switch (y & 1) {
                case 0: r = 1; break;
                case 1: r = 2; break;
            }
            break;
        case 1: r = 3; break;
        case 2: r = 4; break;
        case 3: r = 5; break;
    }
    return r;
}

__attribute__((noinline))
int switch_with_fallthrough(int x) {
    int acc = 0;
    switch (x & 7) {
        case 0:
            acc += 1;
            /* fall through */
        case 1:
            acc += 10;
            break;
        case 2:
        case 3:
            acc += 100;
            break;
        case 4:
            acc += 1000;
            /* fall through */
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
int switch_many_cases(int x) {
    switch (x) {
        case 0:  return 0;
        case 1:  return 1;
        case 2:  return 4;
        case 3:  return 9;
        case 4:  return 16;
        case 5:  return 25;
        case 6:  return 36;
        case 7:  return 49;
        case 8:  return 64;
        case 9:  return 81;
        case 10: return 100;
        case 11: return 121;
        case 12: return 144;
        case 13: return 169;
        case 14: return 196;
        case 15: return 225;
        default: return -1;
    }
}

int main(void) {
    int arr[] = {0, 1, 2, 3};
    return switch_with_default(2) + switch_no_default(1)
         + switch_sparse(100) + switch_in_loop(arr, 4)
         + switch_nested(0, 1) + switch_with_fallthrough(4)
         + switch_many_cases(7);
}

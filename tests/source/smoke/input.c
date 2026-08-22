volatile int sink;

__attribute__((noinline))
int helper_add(int a, int b) {
    return a + b;
}

__attribute__((noinline))
int test_if_no_else(int x) {
    int r = 0;
    if (x > 10) {
        sink = x;
        r = x;
    }
    return r;
}

__attribute__((noinline))
int test_while_loop(int n) {
    int sum = 0;
    while (n > 0) {
        sum += n;
        n--;
    }
    return sum;
}

__attribute__((noinline))
int test_for_loop(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += i;
    }
    return sum;
}

__attribute__((noinline))
int test_do_while(int n) {
    int x = 1;
    do {
        x *= 2;
        n--;
    } while (n > 0);
    return x;
}

__attribute__((noinline))
int test_call(int x) {
    return helper_add(x, 1);
}

__attribute__((noinline))
int test_switch(int x) {
    switch (x) {
        case 0: return 10;
        case 1: return 20;
        case 2: return 30;
        case 3: return 40;
        default: return -1;
    }
}

int main(void) {
    return test_if_no_else(42) + test_while_loop(5) + test_call(9);
}

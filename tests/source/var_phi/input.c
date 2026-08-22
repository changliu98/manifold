/* var_phi: PHI node and control flow merge tests.
 * Tests variable recovery at control flow join points.
 */

volatile int sink;

__attribute__((noinline))
int test_simple_phi(int x) {
    int a;
    if (x > 0) {
        a = 1;
    } else {
        a = 2;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_same_base(int x, int y) {
    int a;
    if (x > 0) {
        a = y + 1;
    } else {
        a = y + 2;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_different_ops(int x, int y) {
    int a;
    if (x > 0) {
        a = y * 2;
    } else {
        a = y / 2;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_nested_phi(int x, int y) {
    int a;
    if (x > 0) {
        if (y > 0) {
            a = 1;
        } else {
            a = 2;
        }
    } else {
        if (y > 0) {
            a = 3;
        } else {
            a = 4;
        }
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_with_use(int x, int y) {
    int a = y;
    if (x > 0) {
        a = a + 1;
    } else {
        a = a - 1;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_multiple_phi(int x) {
    int a, b;
    if (x > 0) {
        a = 1;
        b = 2;
    } else {
        a = 3;
        b = 4;
    }
    sink = a + b;
    return a + b;
}

__attribute__((noinline))
int test_phi_chain(int x) {
    int a;
    if (x > 0) {
        a = 1;
    } else {
        a = 2;
    }
    int b;
    if (a > 1) {
        b = a + 10;
    } else {
        b = a + 20;
    }
    sink = b;
    return b;
}

__attribute__((noinline))
int test_phi_three_way(int x) {
    int a;
    if (x > 10) {
        a = 1;
    } else if (x > 0) {
        a = 2;
    } else {
        a = 3;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_early_exit(int x) {
    int a = 0;
    if (x < 0) {
        return -1;
    }
    if (x > 10) {
        a = 1;
    } else {
        a = 2;
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_with_call(int x, int y) {
    int a;
    if (x > 0) {
        a = test_simple_phi(y);
    } else {
        a = test_simple_phi(-y);
    }
    sink = a;
    return a;
}

__attribute__((noinline))
int test_phi_mixed_sources(int x, int y, int z) {
    int a;
    if (x > 0) {
        a = y;
    } else {
        a = z;
    }
    sink = a;
    return a * 2;
}

__attribute__((noinline))
int test_phi_partially_dead(int x) {
    int a;
    int b = 100;
    if (x > 0) {
        a = 1;
        b = 200;
    } else {
        a = 2;
    }
    sink = a;
    return a + b;
}

int main(void) {
    return test_simple_phi(1) + test_phi_same_base(1, 5)
         + test_phi_different_ops(1, 10) + test_nested_phi(1, 1)
         + test_phi_with_use(1, 5) + test_multiple_phi(1)
         + test_phi_chain(1) + test_phi_three_way(5)
         + test_phi_early_exit(5) + test_phi_with_call(1, 3)
         + test_phi_mixed_sources(1, 5, 10) + test_phi_partially_dead(1);
}

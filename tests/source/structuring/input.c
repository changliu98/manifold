/* structuring: control flow structuring quality tests.
 * Inspired by angr's goto elimination tests, if-else-if chain tests,
 * short-circuit boolean handling, and return deduplication.
 * angr tests: test_decompilation_excessive_goto_removal,
 * test_ifelseif_x8664, test_decompiling_short_circuit_O0_func_1/2,
 * test_return_deduplication. */

volatile int sink;

/* angr test_ifelseif_x8664: if-else-if chain recovery */
__attribute__((noinline))
int if_else_if_chain(int x) {
    if (x == 1) {
        sink = 10;
        return 10;
    } else if (x == 2) {
        sink = 20;
        return 20;
    } else if (x == 3) {
        sink = 30;
        return 30;
    } else if (x == 4) {
        sink = 40;
        return 40;
    } else {
        sink = -1;
        return -1;
    }
}

/* angr test_decompilation_excessive_goto_removal: no gotos needed */
__attribute__((noinline))
int no_goto_diamond(int x, int y) {
    int r;
    if (x > 0) {
        if (y > 0) {
            r = x + y;
        } else {
            r = x - y;
        }
    } else {
        if (y > 0) {
            r = y - x;
        } else {
            r = -(x + y);
        }
    }
    sink = r;
    return r;
}

/* angr test_decompiling_short_circuit_O0_func_1: short-circuit without goto */
__attribute__((noinline))
int short_circuit_and(int a, int b, int c) {
    if (a > 0 && b > 0 && c > 0) {
        sink = 1;
        return a + b + c;
    }
    sink = 0;
    return 0;
}

__attribute__((noinline))
int short_circuit_or(int a, int b, int c) {
    if (a < 0 || b < 0 || c < 0) {
        sink = -1;
        return -1;
    }
    sink = 1;
    return a + b + c;
}

/* angr test_return_deduplication: should fold to minimal returns */
__attribute__((noinline))
int single_exit_value(int x) {
    int r;
    if (x > 100) {
        r = 100;
    } else if (x < 0) {
        r = 0;
    } else {
        r = x;
    }
    return r;
}

/* angr test_decompiling_1after909_doit: no goto in complex control flow */
__attribute__((noinline))
int complex_no_goto(int x, int y) {
    int acc = 0;
    if (x > 0) {
        acc += x;
        if (y > 0) {
            acc *= y;
        }
        acc += 1;
    } else {
        acc = y * 2;
    }
    if (acc > 50) {
        acc = 50;
    }
    sink = acc;
    return acc;
}

/* multiple early returns with side effects -- tests eager return handling
 * angr test_sensitive_eager_returns */
__attribute__((noinline))
int guard_chain(int x) {
    if (x < 0) {
        sink = -1;
        return -1;
    }
    if (x == 0) {
        sink = 0;
        return 0;
    }
    if (x > 1000) {
        sink = 1000;
        return 1000;
    }
    if (x % 2 == 0) {
        sink = x / 2;
        return x / 2;
    }
    sink = x;
    return x;
}

/* deeply nested if-else with consistent structure */
__attribute__((noinline))
int classify(int x, int y) {
    if (x > 0) {
        if (y > 0) {
            return 1; /* quadrant I */
        } else if (y < 0) {
            return 4; /* quadrant IV */
        } else {
            return 5; /* positive x-axis */
        }
    } else if (x < 0) {
        if (y > 0) {
            return 2; /* quadrant II */
        } else if (y < 0) {
            return 3; /* quadrant III */
        } else {
            return 6; /* negative x-axis */
        }
    } else {
        if (y > 0) {
            return 7; /* positive y-axis */
        } else if (y < 0) {
            return 8; /* negative y-axis */
        } else {
            return 0; /* origin */
        }
    }
}

int main(void) {
    return if_else_if_chain(3) + no_goto_diamond(1, -2)
         + short_circuit_and(1, 2, 3) + short_circuit_or(-1, 2, 3)
         + single_exit_value(50) + complex_no_goto(10, 5)
         + guard_chain(42) + classify(1, -1);
}

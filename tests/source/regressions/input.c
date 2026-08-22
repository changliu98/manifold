volatile int sink;

typedef int (*binop_t)(int, int);

struct Pair {
    int left;
    int right;
};

struct Frame {
    struct Pair pairs[4];
    int bias;
    binop_t op;
};

__attribute__((noinline))
int add_op(int a, int b) {
    return a + b;
}

__attribute__((noinline))
int xor_op(int a, int b) {
    return (a ^ b) + 3;
}

__attribute__((noinline))
int guard(int x) {
    if (x < 0) {
        sink = -x;
        return x - 11;
    }
    sink = x;
    return x + 11;
}

__attribute__((noinline))
int test_early_return_ladder(int x) {
    if (x < 0) {
        sink = -1;
        return -1;
    }
    if (x == 0) {
        sink = 0;
        return 0;
    }
    if (x > 99) {
        sink = 99;
        return 99;
    }
    sink = x;
    return x + 1;
}

__attribute__((noinline))
int test_nested_if_chain(int x, int y, int z) {
    if (x > 0) {
        if (y > 0) {
            if (z > 0) {
                sink = 1;
                return 1;
            }
            sink = 2;
            return 2;
        }
        sink = 3;
        return 3;
    }
    sink = 4;
    return 4;
}

__attribute__((noinline))
int dispatch(struct Frame *frame, int seed) {
    int acc = seed;
    for (int i = 0; i < 4; ++i) {
        int left = frame->pairs[i].left;
        int right = frame->pairs[i].right;
        switch ((left ^ right ^ i) & 3) {
            case 0:
                acc += frame->op(left, right);
                break;
            case 1:
                if (left > right) {
                    acc -= left - right;
                } else {
                    acc += right - left;
                }
                break;
            case 2:
                do {
                    acc ^= left + right + i;
                    left--;
                } while (left > right && left > 0);
                break;
            default:
                while (right > 0) {
                    acc += left;
                    if (acc & 1) {
                        break;
                    }
                    right--;
                }
                break;
        }
        if ((acc & 7) == 3) {
            continue;
        }
        if (acc < -50) {
            return acc + frame->bias;
        }
    }
    return acc + frame->bias;
}

__attribute__((noinline))
int test_indirect_dispatch(int seed) {
    struct Frame frame = {
        .pairs = {{1, 2}, {5, 1}, {7, 3}, {4, 4}},
        .bias = 9,
        .op = (seed & 1) ? add_op : xor_op,
    };
    return dispatch(&frame, seed);
}

__attribute__((noinline))
int test_switch_fallthrough(int tag, int x) {
    int acc = 0;
    switch (tag & 7) {
        case 0:
            acc += x;
        case 1:
            acc ^= 3;
            break;
        case 2:
        case 3:
            acc -= 7;
            if (x > 0) {
                acc += x;
                break;
            }
            acc = -acc;
            break;
        default:
            acc = guard(x);
            break;
    }
    return acc;
}

__attribute__((noinline))
int test_nested_loop_break_continue(int n) {
    int acc = 0;
    for (int i = 0; i < n; ++i) {
        int j = i;
        while (j >= 0) {
            if (((i + j) & 1) == 0) {
                j--;
                continue;
            }
            acc += i - j;
            if (acc > 20) {
                break;
            }
            if (acc < -10) {
                return acc;
            }
            j -= 2;
        }
        if (acc > 20) {
            break;
        }
    }
    return acc;
}

__attribute__((noinline))
int test_struct_pointer_alias(int idx) {
    struct Pair pairs[3] = {{1, 10}, {2, 20}, {3, 30}};
    struct Pair *slot = &pairs[idx % 3];
    int *base = &slot->left;
    base[0] += base[1];
    if (base[0] > 25) {
        sink = base[0];
    }
    return slot->left;
}

int main(void) {
    return test_early_return_ladder(4)
        + test_nested_if_chain(1, 2, 3)
        + test_indirect_dispatch(5)
        + test_switch_fallthrough(2, 7)
        + test_nested_loop_break_continue(6)
        + test_struct_pointer_alias(1);
}

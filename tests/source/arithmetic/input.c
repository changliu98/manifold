volatile int sink;

__attribute__((noinline))
int test_add_sub(int a, int b) {
    int x = a + b;
    int y = a - b;
    sink = x;
    return x + y;
}

__attribute__((noinline))
int test_mul_div(int a, int b) {
    if (b == 0) return 0;
    int q = a / b;
    int r = a % b;
    sink = q;
    return q * b + r;
}

__attribute__((noinline))
int test_bitwise(int a, int b) {
    int x = a & b;
    int y = a | b;
    int z = a ^ b;
    sink = x + y;
    return z;
}

__attribute__((noinline))
int test_shift(int a, int n) {
    int left = a << n;
    int right = a >> n;
    sink = left;
    return right;
}

__attribute__((noinline))
long test_long_arith(long a, long b) {
    long x = a * b;
    long y = a + b;
    sink = (int)x;
    return x - y;
}

__attribute__((noinline))
unsigned test_unsigned(unsigned a, unsigned b) {
    unsigned q = a / b;
    unsigned r = a % b;
    sink = (int)q;
    return r;
}

__attribute__((noinline))
int test_negate(int x) {
    int neg = -x;
    int inv = ~x;
    sink = neg;
    return inv;
}

int main(void) {
    return test_add_sub(3, 4) + test_mul_div(10, 3)
         + test_bitwise(0xf0, 0x3c) + test_shift(16, 2)
         + (int)test_long_arith(100L, 200L)
         + (int)test_unsigned(17u, 5u)
         + test_negate(42);
}

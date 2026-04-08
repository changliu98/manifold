volatile int sink;

__attribute__((noinline))
int test_six_args(int a, int b, int c, int d, int e, int f) {
    sink = a + d;
    return a + b + c + d + e + f;
}

__attribute__((noinline))
int test_seven_args(int a, int b, int c, int d, int e, int f, int g) {
    sink = g;
    return a - b + c - d + e - f + g;
}

__attribute__((noinline))
long test_mixed_types(int a, long b, int c, long d) {
    long r = (long)a + b + (long)c + d;
    sink = (int)r;
    return r;
}

__attribute__((noinline))
int test_pass_through(int x) {
    return test_six_args(x, x+1, x+2, x+3, x+4, x+5);
}

__attribute__((noinline))
int test_void_return(int x) {
    sink = x * 2;
    return 0;
}

__attribute__((noinline))
int test_chain(int x) {
    int a = test_void_return(x);
    int b = test_six_args(x, a, x, a, x, a);
    return b;
}

int main(void) {
    return test_six_args(1,2,3,4,5,6)
         + test_seven_args(1,2,3,4,5,6,7)
         + (int)test_mixed_types(1, 2L, 3, 4L)
         + test_pass_through(10)
         + test_chain(5);
}

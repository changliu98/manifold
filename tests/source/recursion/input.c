volatile int sink;

__attribute__((noinline))
int test_factorial(int n) {
    if (n <= 1) return 1;
    return n * test_factorial(n - 1);
}

__attribute__((noinline))
int test_fibonacci(int n) {
    if (n <= 0) return 0;
    if (n == 1) return 1;
    return test_fibonacci(n - 1) + test_fibonacci(n - 2);
}

__attribute__((noinline))
int test_gcd(int a, int b) {
    if (b == 0) return a;
    return test_gcd(b, a % b);
}

__attribute__((noinline))
int test_iterative_factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; i++) {
        result *= i;
    }
    return result;
}

__attribute__((noinline))
int test_mutual_even(int n);
__attribute__((noinline))
int test_mutual_odd(int n);

int test_mutual_even(int n) {
    if (n == 0) return 1;
    return test_mutual_odd(n - 1);
}

int test_mutual_odd(int n) {
    if (n == 0) return 0;
    return test_mutual_even(n - 1);
}

int main(void) {
    return test_factorial(5) + test_fibonacci(6)
         + test_gcd(48, 18) + test_iterative_factorial(5)
         + test_mutual_even(4);
}

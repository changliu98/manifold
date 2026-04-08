volatile int sink;

__attribute__((noinline))
int test_deref_write(int *p, int val) {
    *p = val;
    sink = *p;
    return *p;
}

__attribute__((noinline))
int test_array_sum(int *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
void test_swap(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

__attribute__((noinline))
int test_out_param(int x, int *out) {
    *out = x * 2;
    return x + 1;
}

__attribute__((noinline))
int test_ptr_arith(int *base, int offset) {
    int *p = base + offset;
    sink = *p;
    return *(p + 1);
}

__attribute__((noinline))
int test_null_check(int *p) {
    if (p == 0)
        return -1;
    sink = *p;
    return *p;
}

int main(void) {
    int arr[] = {1, 2, 3, 4, 5};
    int a = 10, b = 20, out = 0;
    test_deref_write(&a, 99);
    test_swap(&a, &b);
    test_out_param(5, &out);
    return test_array_sum(arr, 5) + test_ptr_arith(arr, 1)
         + test_null_check(&a);
}

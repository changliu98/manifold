/* var_stack: stack variable recovery tests.
 * Tests local variables stored on the stack.
 */

volatile int sink;

__attribute__((noinline))
int test_local_array_access(int idx) {
    int arr[5] = {10, 20, 30, 40, 50};
    sink = arr[idx];
    return arr[idx];
}

__attribute__((noinline))
int test_local_array_sum(int n) {
    int arr[10];
    for (int i = 0; i < n && i < 10; i++) {
        arr[i] = i * 2;
    }
    int sum = 0;
    for (int i = 0; i < n && i < 10; i++) {
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
int test_address_taken(int x) {
    int a = x;
    int *p = &a;
    *p = x + 1;
    sink = a;
    return a;
}

__attribute__((noinline))
int test_multiple_address_taken(int x, int y) {
    int a = x;
    int b = y;
    int *pa = &a;
    int *pb = &b;
    *pa = *pa + 1;
    *pb = *pb + 2;
    sink = a + b;
    return a + b;
}

__attribute__((noinline))
int test_nested_array_init(int idx1, int idx2) {
    int arr[3][3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
    sink = arr[idx1][idx2];
    return arr[idx1][idx2];
}

struct SmallStruct {
    int a;
    int b;
};

__attribute__((noinline))
int test_local_struct(int x, int y) {
    struct SmallStruct s;
    s.a = x;
    s.b = y;
    sink = s.a + s.b;
    return s.a * s.b;
}

__attribute__((noinline))
int test_struct_array(int idx) {
    struct SmallStruct arr[3];
    arr[0].a = 1; arr[0].b = 2;
    arr[1].a = 3; arr[1].b = 4;
    arr[2].a = 5; arr[2].b = 6;
    sink = arr[idx].a;
    return arr[idx].a + arr[idx].b;
}

__attribute__((noinline))
int test_address_passed_to_func(int x) {
    int a = x;
    int *p = &a;
    sink = *p;
    return *p + 1;
}

__attribute__((noinline))
int test_large_local(int x) {
    int arr[100];
    for (int i = 0; i < 100; i++) {
        arr[i] = x + i;
    }
    int sum = 0;
    for (int i = 0; i < 100; i++) {
        sum += arr[i];
    }
    return sum;
}

__attribute__((noinline))
int test_stack_pointer_escape(int x) {
    int a = x;
    int *p = &a;
    sink = (long)p;
    return *p;
}

__attribute__((noinline))
int test_mixed_stack_reg(int x, int y, int z) {
    int a = x + y;
    int b = y + z;
    int arr[3] = {a, b, a + b};
    sink = arr[0] + arr[1] + arr[2];
    return arr[0] * arr[1] + arr[2];
}

__attribute__((noinline))
int test_conditional_stack_write(int x, int cond) {
    int arr[4] = {0, 0, 0, 0};
    if (cond > 0) {
        arr[0] = x;
        arr[1] = x + 1;
    } else {
        arr[2] = x;
        arr[3] = x + 1;
    }
    return arr[0] + arr[1] + arr[2] + arr[3];
}

__attribute__((noinline))
int test_stack_in_loop(int n) {
    int result = 0;
    for (int i = 0; i < n; i++) {
        int arr[4] = {i, i+1, i+2, i+3};
        result += arr[0] + arr[3];
    }
    return result;
}

int main(void) {
    return test_local_array_access(2) + test_local_array_sum(5)
         + test_address_taken(10) + test_multiple_address_taken(5, 10)
         + test_nested_array_init(1, 1) + test_local_struct(3, 4)
         + test_struct_array(1) + test_address_passed_to_func(7)
         + test_large_local(1) + test_stack_pointer_escape(42)
         + test_mixed_stack_reg(1, 2, 3) + test_conditional_stack_write(5, 1)
         + test_stack_in_loop(5);
}

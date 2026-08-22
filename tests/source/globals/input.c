volatile int sink;

int global_counter = 0;
int global_array[8] = {10, 20, 30, 40, 50, 60, 70, 80};
const char *global_message = "hello world";

__attribute__((noinline))
int test_read_global(void) {
    return global_counter;
}

__attribute__((noinline))
void test_write_global(int val) {
    global_counter = val;
    sink = global_counter;
}

__attribute__((noinline))
int test_global_array_access(int idx) {
    if (idx < 0 || idx >= 8) return -1;
    return global_array[idx];
}

__attribute__((noinline))
int test_increment_global(void) {
    global_counter += 1;
    return global_counter;
}

__attribute__((noinline))
int test_string_length(const char *s) {
    int len = 0;
    while (*s != '\0') {
        len++;
        s++;
    }
    return len;
}

__attribute__((noinline))
int test_use_global_string(void) {
    return test_string_length(global_message);
}

int main(void) {
    test_write_global(42);
    return test_read_global() + test_global_array_access(3)
         + test_increment_global() + test_use_global_string();
}

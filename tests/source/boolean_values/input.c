#include <stdbool.h>
#include <stdio.h>

/* Byte storage whose every definition is a comparison or 0/1 is a _Bool. */
__attribute__((noinline)) int count_positive(const int *values, int n) {
    bool seen_negative = false;
    int count = 0;
    for (int i = 0; i < n; i++) {
        bool positive = values[i] > 0;
        if (positive)
            count++;
        if (values[i] < 0)
            seen_negative = true;
    }
    return seen_negative ? -count : count;
}

/* Negation keeps a boolean web boolean around the loop. */
__attribute__((noinline)) int toggle(int n) {
    bool on = false;
    for (int i = 0; i < n; i++)
        on = !on;
    return on;
}

/* A byte that counts is not boolean, even though it starts at 0. */
__attribute__((noinline)) int byte_counter(const char *s) {
    unsigned char count = 0;
    while (*s++)
        count++;
    return count;
}

/* A byte whose address escapes may be written through the pointer. */
__attribute__((noinline)) void overwrite(unsigned char *p) {
    *p = 7;
}

__attribute__((noinline)) int escaped_mark(int x) {
    unsigned char mark = x > 0;
    overwrite(&mark);
    return mark;
}

int main(void) {
    int values[3] = {1, -2, 3};
    printf("%d %d %d %d\n", count_positive(values, 3), toggle(3), byte_counter("abc"),
           escaped_mark(1));
    return 0;
}

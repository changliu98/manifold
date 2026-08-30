#include <stdint.h>

struct pair {
    int64_t left;
    int64_t right;
};

static volatile struct pair pairs[] = {
    {31, 11},
    {INT64_MAX, 1},
    {INT64_MIN, -1},
    {-77, 19},
};

__attribute__((noinline))
static int branch_on_overflow(int64_t left, int64_t right) {
    unsigned char result;
    __asm__ volatile(
        "addq %[right], %[left]\n\t"
        "jo 1f\n\t"
        "movb $11, %[result]\n\t"
        "jmp 2f\n"
        "1: movb $97, %[result]\n"
        "2:"
        : [left] "+r"(left), [result] "=&q"(result)
        : [right] "r"(right)
        : "cc");
    return result;
}

__attribute__((noinline))
static int branch_on_no_overflow(int64_t left, int64_t right) {
    unsigned char result;
    __asm__ volatile(
        "addq %[right], %[left]\n\t"
        "jno 1f\n\t"
        "movb $89, %[result]\n\t"
        "jmp 2f\n"
        "1: movb $17, %[result]\n"
        "2:"
        : [left] "+r"(left), [result] "=&q"(result)
        : [right] "r"(right)
        : "cc");
    return result;
}

int main(int argc, char **argv) {
    (void)argv;
    unsigned index = (unsigned)(argc - 1) & 3u;
    int64_t left = pairs[index].left;
    int64_t right = pairs[index].right;
    return (branch_on_overflow(left, right)
            + 3 * branch_on_no_overflow(left, right)) & 255;
}

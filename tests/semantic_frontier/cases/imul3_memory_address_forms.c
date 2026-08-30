#include <stddef.h>

static int frontier_base_words[4] = {2, 3, 5, 7};
static int frontier_indexed_words[4] = {11, 13, 17, 19};
__attribute__((used)) static int frontier_rip_word = 23;

__attribute__((noinline))
static int frontier_imul3_base(const int *base) {
    int result;
    __asm__ volatile(
        "imull $3, (%[base]), %[result]"
        : [result] "=&r"(result)
        : [base] "r"(base)
        : "cc", "memory");
    return result;
}

__attribute__((noinline))
static int frontier_imul3_indexed(const int *base, size_t index) {
    int result;
    __asm__ volatile(
        "imull $5, -8(%[base],%[index],4), %[result]"
        : [result] "=&r"(result)
        : [base] "r"(base), [index] "r"(index)
        : "cc", "memory");
    return result;
}

__attribute__((noinline))
static int frontier_imul3_stack(int value) {
    int result;
    __asm__ volatile(
        "movl %[value], -4(%%rsp)\n\t"
        "imull $7, -4(%%rsp), %[result]"
        : [result] "=&r"(result)
        : [value] "r"(value)
        : "cc", "memory");
    return result;
}

__attribute__((noinline))
static int frontier_imul3_rip(void) {
    int result;
    __asm__ volatile(
        "imull $131, frontier_rip_word(%%rip), %[result]"
        : [result] "=&r"(result)
        :
        : "cc", "memory");
    return result;
}

int main(int argc, char **argv) {
    (void)argv;
    size_t index = (size_t)(argc - 1) & 3U;
    int total = frontier_imul3_base(frontier_base_words + index);
    total += frontier_imul3_indexed(frontier_indexed_words + 2, index);
    total += frontier_imul3_stack(argc + 1);
    total += frontier_imul3_rip();
    return total & 255;
}

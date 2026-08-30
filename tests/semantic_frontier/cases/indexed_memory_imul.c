#include <stddef.h>

__attribute__((noinline))
static int frontier_indexed_imul(
    const int *base,
    size_t index,
    int accumulator
) {
    __asm__ volatile(
        "imull -8(%[base],%[index],4), %[accumulator]"
        : [accumulator] "+&r"(accumulator)
        : [base] "r"(base), [index] "r"(index)
        : "cc", "memory");
    return accumulator > 50 ? accumulator : 50;
}

int main(int argc, char **argv) {
    (void)argv;
    int frontier_words[4] = {3, 5, 11, 13};
    size_t index = (size_t)(argc - 1) & 3U;
    return frontier_indexed_imul(frontier_words + 2, index, 7);
}

#include <stddef.h>
#include <stdint.h>

static volatile uint32_t frontier_words[4] = {
    UINT32_C(0x00000000),
    UINT32_C(0x80000000),
    UINT32_C(0x01010101),
    UINT32_C(0xffffffff),
};

__attribute__((noinline))
static unsigned frontier_scaled_test(
    const volatile uint32_t *base,
    size_t index,
    uint32_t mask
) {
    unsigned char is_zero;
    unsigned char is_nonzero;
    unsigned char is_sign;
    unsigned char is_nonsign;
    unsigned char is_parity;
    unsigned char is_nonparity;

    __asm__ volatile(
        "testl %k[mask], (%[base],%[index],4)\n\t"
        "setz %[zero]\n\t"
        "setnz %[nonzero]\n\t"
        "sets %[sign]\n\t"
        "setns %[nonsign]\n\t"
        "setp %[parity]\n\t"
        "setnp %[nonparity]"
        : [zero] "=q"(is_zero),
          [nonzero] "=q"(is_nonzero),
          [sign] "=q"(is_sign),
          [nonsign] "=q"(is_nonsign),
          [parity] "=q"(is_parity),
          [nonparity] "=q"(is_nonparity)
        : [base] "r"(base), [index] "r"(index), [mask] "r"(mask)
        : "cc", "memory");

    return (unsigned)is_zero
         | ((unsigned)is_nonzero << 1)
         | ((unsigned)is_sign << 2)
         | ((unsigned)is_nonsign << 3)
         | ((unsigned)is_parity << 4)
         | ((unsigned)is_nonparity << 5);
}

int main(int argc, char **argv) {
    (void)argv;
    unsigned index = (unsigned)(argc - 1) & 3U;
    uint32_t mask = index == 3U ? UINT32_C(0x7fffffff) : UINT32_MAX;
    return (int)frontier_scaled_test(frontier_words, index, mask);
}

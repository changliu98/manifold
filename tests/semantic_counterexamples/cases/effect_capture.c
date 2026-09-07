#include <stdint.h>

__attribute__((noinline))
static uint64_t choose(unsigned input)
{
    unsigned char cell = (unsigned char) input;
    uint64_t value = UINT64_C(0x5500000011);
    uint64_t replacement = UINT64_C(0xaa00000053);
#ifdef WORD_RESULT
    __asm__ volatile (
        "cmpb $1, %[cell]\n\t"
        "movb $0, %[cell]\n\t"
        "cmovns %k[replacement], %k[value]"
        : [value] "+r" (value), [cell] "+m" (cell)
        : [replacement] "r" (replacement)
        : "cc", "memory");
#else
    __asm__ volatile (
        "cmpb $1, %[cell]\n\t"
        "movb $0, %[cell]\n\t"
        "cmovns %[replacement], %[value]"
        : [value] "+r" (value), [cell] "+m" (cell)
        : [replacement] "r" (replacement)
        : "cc", "memory");
#endif
    return value;
}

int main(int argc, char **argv)
{
    (void) argv;
    uint64_t value = choose(argc == 1 ? 128u : 0u);
    return (unsigned)((value & 255u) + ((value >> 32) & 255u));
}

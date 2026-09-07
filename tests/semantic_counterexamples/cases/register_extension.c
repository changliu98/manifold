#include <stdint.h>

__attribute__((noinline))
static uint64_t extend(uint64_t value)
{
#if defined(WORD_SOURCE) && defined(QUAD_RESULT)
    __asm__ volatile ("movzwq %w[value], %[value]"
                      : [value] "+a" (value));
#elif defined(WORD_SOURCE)
    __asm__ volatile ("movzwl %w[value], %k[value]"
                      : [value] "+a" (value));
#elif defined(QUAD_RESULT)
    __asm__ volatile ("movzbq %b[value], %[value]"
                      : [value] "+a" (value));
#else
    __asm__ volatile ("movzbl %b[value], %k[value]"
                      : [value] "+a" (value));
#endif
    return value;
}

int main(int argc, char **argv)
{
    (void) argv;
    uint64_t input = argc == 1 ? UINT64_C(0x88776655aabbcc81)
                               : UINT64_C(0x1234567890abcd7e);
    uint64_t value = extend(input);
#ifdef WORD_SOURCE
    return value != (input & UINT64_C(65535));
#else
    return value != (input & UINT64_C(255));
#endif
}

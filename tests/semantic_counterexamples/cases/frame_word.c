#include <stdint.h>

__attribute__((noinline))
static void fill_word(uint32_t *p, unsigned value)
{
    *p = 0u - value;
    __asm__ volatile ("" : : "r" (p) : "memory");
}

int main(int argc, char **argv)
{
    (void) argv;
    uint32_t word;
    unsigned input = (unsigned) argc;
    fill_word(&word, input);
    uint64_t wide = word;
    return (unsigned)(((wide * 3u + input) >> 32) ^ (wide & 255u)) & 255u;
}

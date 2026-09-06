#include <stdint.h>

__attribute__((noinline))
static unsigned word_bytes(const unsigned char *p)
{
    __asm__ volatile ("" : : "r" (p) : "memory");
    return p[0] + 3u * p[7];
}

int main(int argc, char **argv)
{
    (void) argc;
    (void) argv;
    uint64_t word = UINT32_MAX;
    return word_bytes((const unsigned char *) &word) & 255u;
}

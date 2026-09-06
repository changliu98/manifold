#include <stdint.h>
#include <string.h>

__attribute__((noinline))
static void fill(unsigned char *bytes, unsigned value)
{
    uint32_t word = value * 0x01020304u;
    memcpy(bytes, &word, sizeof word);
    bytes[5] = (unsigned char)(0x80u | (value & 31u));
    __asm__ volatile ("" : : "r" (bytes) : "memory");
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char bytes[16];
    fill(bytes, (unsigned) argc);
    uint32_t word;
    memcpy(&word, bytes, sizeof word);
#ifdef LINEAR_READ
#ifdef SIGNED_READ
    unsigned high = (unsigned)(int)(signed char) bytes[5];
#else
    unsigned high = bytes[5];
#endif
    return ((word & 127u) + (high >> 1)) & 255u;
#else
#ifdef SIGNED_READ
    unsigned high = (signed char) bytes[5] < 0;
#else
    unsigned high = bytes[5] >> 7;
#endif
    return ((word & 127u) + 23u * high) & 255u;
#endif
}

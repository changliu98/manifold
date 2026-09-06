#include <stdint.h>

__attribute__((noinline))
static void write_view(unsigned value, unsigned char *buffer)
{
    __asm__ volatile ("" : : "r" (buffer) : "memory");
    buffer[0] = 10 + (value & 15);
    buffer[1] = 66;
}

__attribute__((noinline))
static unsigned read_base(const unsigned char *buffer)
{
    __asm__ volatile ("" : : "r" (buffer) : "memory");
    return buffer[3] + 2u * buffer[4];
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char buffer[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    write_view((unsigned) argc, buffer + ((unsigned) argc & 3u));
#ifdef DIRECT_READ
    return buffer[3] + 2u * buffer[4];
#else
    return read_base(buffer);
#endif
}

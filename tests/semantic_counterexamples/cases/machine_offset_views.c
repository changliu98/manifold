#include <stdint.h>

__attribute__((noinline))
static unsigned char *format_bytes(unsigned value, unsigned char *buffer)
{
    __asm__ volatile ("" : : "r" (buffer) : "memory");
    buffer[30] = 'A' + (value & 15);
    buffer[31] = 'B';
    buffer[32] = 0;
    return buffer + 30;
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char buffer[64];
    unsigned char *text;
#ifdef CONSTANT_VIEWS
    if (argc & 1) {
        text = format_bytes((unsigned) argc, buffer + 1);
        *--text = '-';
    } else {
        text = format_bytes((unsigned) argc, buffer);
    }
#else
    unsigned offset = INDEX_EXPR;
#ifdef GUARDED_INDEX
    if (offset > 20)
        return 200;
#endif
    text = format_bytes((unsigned) argc, buffer + offset);
    if (argc & 1)
        *--text = '-';
#endif
    return (unsigned) text[0] + (unsigned) text[1];
}

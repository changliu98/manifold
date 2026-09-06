#include <stdint.h>

/* A serialized header with two independently observed sliding windows. */
__attribute__((noinline))
static unsigned header_sum(const unsigned char *p)
{
    __asm__ volatile ("" : : "r" (p) : "memory");
    return p[0] + 3u * p[3] + 5u * p[7] + 7u * p[15];
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char packet[24] = {
        3, 5, 7, 11, 13, 17, 19, 23,
        29, 31, 37, 41, 43, 47, 53, 59,
        61, 67, 71, 73, 79, 83, 89, 97
    };
    unsigned shift = (unsigned) argc & 3u;
    unsigned first = header_sum(packet + shift);
    unsigned second = header_sum(packet + (3u - shift));
    return (first ^ (second >> 2)) & 255u;
}

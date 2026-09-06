#include <stdint.h>
#include <string.h>

/* Fixed observation crosses a dynamic, four-byte little-endian write. */
__attribute__((noinline))
static void patch_lane(unsigned char *p, uint32_t value)
{
    __asm__ volatile ("" : : "r" (p) : "memory");
    memcpy(p, &value, sizeof value);
}

__attribute__((noinline))
static unsigned lane_checksum(const unsigned char *p)
{
    __asm__ volatile ("" : : "r" (p) : "memory");
    return p[2] + 3u * p[5] + 7u * p[8] + 11u * p[10];
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char bytes[16] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
    uint32_t value = 0x10203040u + (unsigned) argc;
    patch_lane(bytes + ((unsigned) argc & 7u), value);
    return lane_checksum(bytes) & 255u;
}

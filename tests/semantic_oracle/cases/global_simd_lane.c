#include <stdint.h>

typedef uint32_t lanes4 __attribute__((vector_size(16)));

static volatile lanes4 global_lanes __attribute__((aligned(16))) = {
    0x10203040u, 0x55667788u, 0x90abcdefu, 0xfedcba09u
};
static volatile unsigned char global_bytes[16] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59
};

__attribute__((noinline))
static uint32_t select_mixed_lane(unsigned index) {
    lanes4 bias = {7u, 11u, 13u, 17u};
    lanes4 mask = {0x01020304u, 0x11121314u, 0x21222324u, 0x31323334u};
    lanes4 mixed = (global_lanes + bias) ^ mask;
    uint32_t lane = mixed[index & 3u];
    uint32_t byte_mix = (uint32_t)global_bytes[1]
                      + ((uint32_t)global_bytes[7] << 3)
                      + ((uint32_t)global_bytes[13] << 9);
    return lane ^ byte_mix;
}

int main(int argc, char **argv) {
    (void)argv;
    return (int)(select_mixed_lane((unsigned)(argc - 1)) & 255u);
}

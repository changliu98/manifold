#include <stdint.h>
#include <stdio.h>

__attribute__((noinline)) uint64_t mixed_width_chain(uint32_t input) {
    volatile uint32_t cell = input;
    uint64_t product = (uint64_t)cell * UINT64_C(1321528399);
    uint32_t high = product >> 32;
    cell = high ^ UINT32_C(0x81234567);
    product = (uint64_t)cell * UINT64_C(65537);
    return product ^ (product >> 32);
}

__attribute__((noinline)) uint64_t branch_values(uint32_t input, int choose) {
    uint64_t value;
    if (choose)
        value = (uint64_t)input * UINT64_C(0x100000001);
    else
        value = input & UINT32_C(0x7fffffff);
    uint64_t result = value + 3;
    value = input & 255;
    return result ^ value;
}

__attribute__((noinline)) uint64_t loop_values(uint32_t input) {
    uint64_t result = 1;
    for (unsigned i = 0; i < 4; ++i) {
        uint64_t value = (uint64_t)(input + i) * UINT64_C(65537);
        result ^= value;
    }
    return result;
}

int main(void) {
    uint32_t inputs[] = {0, 1, 26, 255, 65535, 0x7fffffff, 0x80000000, 0xffffffff};
    for (unsigned i = 0; i < sizeof(inputs) / sizeof(inputs[0]); ++i) {
        printf("%llu %llu %llu %llu\n",
               (unsigned long long)mixed_width_chain(inputs[i]),
               (unsigned long long)branch_values(inputs[i], 0),
               (unsigned long long)branch_values(inputs[i], 1),
               (unsigned long long)loop_values(inputs[i]));
    }
    return 0;
}

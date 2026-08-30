#include <stddef.h>
#include <stdint.h>

typedef union {
    uint64_t bits;
    double value;
} frontier_double_slot;

static volatile frontier_double_slot frontier_source[6] = {
    {.bits = UINT64_C(0x3ff0000000000000)},
    {.bits = UINT64_C(0x8000000000000000)},
    {.bits = UINT64_C(0x7ff8000000001234)},
    {.bits = UINT64_C(0x0000000000000001)},
    {.bits = UINT64_C(0xfff0000000000000)},
    {.bits = UINT64_C(0x400921fb54442d18)},
};

static volatile frontier_double_slot frontier_legacy_destination[6];
static volatile frontier_double_slot frontier_avx_destination[6];

__attribute__((noinline))
static uint64_t frontier_legacy_indexed_move(
    volatile frontier_double_slot *destination,
    const volatile frontier_double_slot *source,
    size_t source_index,
    size_t destination_index
) {
    __asm__ volatile(
        "movsd (%[source],%[source_index],8), %%xmm0\n\t"
        "movsd %%xmm0, (%[destination],%[destination_index],8)"
        :
        : [source] "r"(source),
          [source_index] "r"(source_index),
          [destination] "r"(destination),
          [destination_index] "r"(destination_index)
        : "xmm0", "memory");
    return destination[destination_index].bits;
}

__attribute__((noinline, target("avx")))
static uint64_t frontier_avx_indexed_move(
    volatile frontier_double_slot *destination,
    const volatile frontier_double_slot *source,
    size_t source_index,
    size_t destination_index
) {
    __asm__ volatile(
        "vmovsd (%[source],%[source_index],8), %%xmm1\n\t"
        "vmovsd %%xmm1, (%[destination],%[destination_index],8)"
        :
        : [source] "r"(source),
          [source_index] "r"(source_index),
          [destination] "r"(destination),
          [destination_index] "r"(destination_index)
        : "xmm1", "memory");
    return destination[destination_index].bits;
}

int main(int argc, char **argv) {
    (void)argv;
    size_t legacy_source_index = 1U + ((unsigned)argc & 3U);
    size_t legacy_destination_index = 1U + ((unsigned)(argc + 1) & 3U);
    size_t avx_source_index = 1U + ((unsigned)(argc + 2) & 3U);
    size_t avx_destination_index = 1U + ((unsigned)(argc + 3) & 3U);

    frontier_legacy_destination[legacy_destination_index].bits =
        UINT64_C(0x1122334455667788);
    frontier_avx_destination[avx_destination_index].bits =
        UINT64_C(0x8877665544332211);

    uint64_t legacy_observed = frontier_legacy_indexed_move(
        frontier_legacy_destination,
        frontier_source,
        legacy_source_index,
        legacy_destination_index);
    uint64_t avx_observed = frontier_avx_indexed_move(
        frontier_avx_destination,
        frontier_source,
        avx_source_index,
        avx_destination_index);

    return (int)((legacy_observed ^ avx_observed) & UINT64_C(0xff));
}

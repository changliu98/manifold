#include <stddef.h>
#include <stdint.h>

struct adjacent_arrays {
    uint32_t left[4];
    uint32_t right[4];
};

_Static_assert(offsetof(struct adjacent_arrays, right) == sizeof(uint32_t) * 4,
               "fixture requires adjacent array members");

__attribute__((noinline))
static uint32_t *advance(uint32_t *base, size_t count) {
    return base + count;
}

__attribute__((noinline))
static uint32_t *identity(uint32_t *pointer) {
    return pointer;
}

__attribute__((noinline))
static int pointers_equal(const uint32_t *left, const uint32_t *right) {
    return left == right;
}

int main(int argc, char **argv) {
    (void)argv;
    struct adjacent_arrays values = {
        {7u, 11u, 13u, 17u},
        {19u, 23u, 29u, 31u},
    };
    size_t count = ((unsigned)(argc - 1) & 1u) ? 3u : 4u;
    uint32_t *candidate = advance(values.left, count);
    uint32_t *right_start = identity(values.right);
    int same = pointers_equal(candidate, right_start);
    uint32_t before = candidate[-1];
    return (int)((before + (uint32_t)(same * 97) + values.right[1]) & 255u);
}

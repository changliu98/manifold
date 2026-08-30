#include <stddef.h>
#include <stdint.h>

struct relocated_record {
    uint32_t marker;
    uint16_t flags;
    uint16_t generation;
    uint32_t *pointer;
    uint64_t tail;
};

_Static_assert(offsetof(struct relocated_record, pointer) == 8,
               "fixture requires the relocated pointer at base + 8");

static uint32_t global_words[5] = {
    0x10203040u, 0x21314151u, 0x32425262u, 0x43536373u, 0x54647484u
};

static struct relocated_record global_record = {
    0x13579bdfu,
    0x2468u,
    0x55aau,
    &global_words[2],
    UINT64_C(0x0123456789abcdef),
};

__attribute__((noinline))
static void copy_record(struct relocated_record *out) {
    *out = global_record;
}

__attribute__((noinline))
static uint32_t *load_interior_pointer(const void *base) {
    uint32_t *pointer;
    __builtin_memcpy(&pointer, (const unsigned char *)base + 8, sizeof(pointer));
    return pointer;
}

__attribute__((noinline))
static int same_pointer(const uint32_t *left, const uint32_t *right) {
    return left == right;
}

int main(int argc, char **argv) {
    (void)argv;
    global_words[2] ^= (uint32_t)argc * 0x01010101u;
    struct relocated_record local;
    copy_record(&local);
    uint32_t *pointer = load_interior_pointer(&local);
    uint32_t digest = local.marker;
    digest ^= (uint32_t)local.flags << 8;
    digest ^= (uint32_t)local.generation << 16;
    digest ^= (uint32_t)local.tail ^ (uint32_t)(local.tail >> 32);
    digest ^= pointer[0] + 3u * pointer[1];
    digest ^= same_pointer(pointer, &global_words[2]) ? 0xa5u : 0x5au;
    return (int)(digest & 255u);
}

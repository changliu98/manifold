#include <stdint.h>

__attribute__((noinline))
static void store_u8(uint8_t *out, uint32_t value) {
    *out = (uint8_t)value;
}

__attribute__((noinline))
static void store_u16(uint16_t *out, uint32_t value) {
    *out = (uint16_t)value;
}

__attribute__((noinline))
static void store_u64(uint64_t *out, uint64_t value) {
    *out = value;
}

int main(int argc, char **argv) {
    (void)argv;
    union {
        uint64_t align;
        uint8_t bytes[32];
    } arena;
    for (unsigned i = 0; i < 32; ++i) {
        arena.bytes[i] = (uint8_t)(0xa0u + i);
    }
    uint32_t salt = (uint32_t)argc * 0x01030507u;
    store_u8(&arena.bytes[3], salt ^ 0x5au);
    store_u16((uint16_t *)&arena.bytes[8], salt ^ 0x6b7cu);
    store_u64((uint64_t *)&arena.bytes[16],
              ((uint64_t)salt << 32) ^ UINT64_C(0x1122334455667788));
    uint32_t digest = 0;
    for (unsigned i = 0; i < 32; ++i) {
        digest = (digest * 33u) ^ arena.bytes[i];
    }
    return (int)(digest & 255u);
}

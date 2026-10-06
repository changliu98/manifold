#include <stdint.h>

__attribute__((noinline)) unsigned byte_value(unsigned input) {
    volatile unsigned char cell = input;
    return cell;
}

__attribute__((noinline)) int signed_byte_value(int input) {
    volatile signed char cell = input;
    return cell;
}

__attribute__((noinline)) unsigned short_value(unsigned input) {
    volatile unsigned short cell = input;
    return cell;
}

__attribute__((noinline)) unsigned promoted_byte(unsigned input) {
    volatile unsigned char cell = input;
    return cell + 300;
}

__attribute__((noinline)) uint64_t wide_value(uint64_t input) {
    volatile uint64_t cell = input;
    return cell;
}

__attribute__((noinline)) unsigned forwarded_promoted_byte(unsigned input) {
    return promoted_byte(input);
}

int main(void) {
    if (byte_value(511) != 255 || byte_value(256) != 0)
        return 1;
    if (signed_byte_value(255) != -1 || signed_byte_value(-129) != 127)
        return 2;
    if (short_value(65537) != 1 || short_value(65535) != 65535)
        return 3;
    if (promoted_byte(255) != 555 || promoted_byte(256) != 300)
        return 4;
    if (wide_value(UINT64_C(0x100000001)) != UINT64_C(0x100000001))
        return 5;
    if (forwarded_promoted_byte(255) != 555)
        return 6;
    return 0;
}

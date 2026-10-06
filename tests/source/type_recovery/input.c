#include <stdint.h>
#include <stdio.h>

__attribute__((noinline)) uint32_t word_cell(uint32_t value) {
    volatile uint32_t cell = value;
    cell ^= UINT32_C(0x81234567);
    return cell;
}

__attribute__((noinline)) uint64_t wide_cell(uint64_t value) {
    volatile uint64_t cell = value;
    cell += UINT64_C(0x100000001);
    return cell;
}

__attribute__((noinline)) unsigned byte_cell(unsigned value) {
    volatile unsigned char cell = value;
    return cell;
}

__attribute__((noinline)) int scalar_sink(int value) {
    return value * 3 + 1;
}

__attribute__((noinline)) int signed_byte_argument(int value) {
    volatile signed char cell = value;
    if (cell == 0)
        return 7;
    return scalar_sink(cell);
}

__attribute__((noinline)) char *character_cursor(char *input) {
    char *volatile cursor = input;
    cursor = cursor + 1;
    return cursor;
}

int main(void) {
    char text[] = "ab";
    printf("%u %llu %d\n", word_cell(UINT32_C(0xffffffff)),
           (unsigned long long)wide_cell(UINT64_C(0x100000001)),
           *character_cursor(text));
    printf("%u %u %u\n", byte_cell(257), byte_cell(255), byte_cell(128));
    printf("%d %d\n", signed_byte_argument(128), signed_byte_argument(256));
    return 0;
}

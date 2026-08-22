/* Scalar edge cases: signedness, widening/truncation, boolean normalization,
 * mixed-width arithmetic, and mask/shift idioms. */

volatile int sink;
volatile unsigned usink;
volatile long lsink;

__attribute__((noinline))
int signed_unsigned_compare(int a, unsigned b) {
    int score = 0;
    if ((unsigned)a < b) {
        score += 1;
    }
    if (a < (int)b) {
        score += 2;
    }
    sink = score;
    return score;
}

__attribute__((noinline))
int char_short_extensions(signed char c, unsigned char uc, short s, unsigned short us) {
    int signed_char = c;
    int zero_char = uc;
    int signed_short = s;
    unsigned zero_short = us;
    int mix = signed_char + zero_char;
    int shifted = signed_short >> 3;
    unsigned masked = zero_short & 0xffu;
    sink = shifted;
    usink = masked;
    mix += shifted;
    mix += (int)masked;
    sink = mix;
    return mix;
}

__attribute__((noinline))
int explicit_truncation(int x, unsigned y) {
    unsigned char low = (unsigned char)x;
    signed char high = (signed char)(y >> 8);
    short narrowed = (short)(low + high);
    usink = low;
    sink = high;
    sink = narrowed;
    return (int)narrowed;
}

__attribute__((noinline))
int boolean_normalization(int x, int y) {
    int nonzero = x != 0;
    int in_range = y > 3 && y < 20;
    int normalized = nonzero && in_range;
    sink = normalized;
    return normalized;
}

__attribute__((noinline))
long mixed_width_arithmetic(long base, int delta, unsigned short scale) {
    long widened = base + (long)delta;
    unsigned scaled = (unsigned)scale * 17u;
    long result = widened - (long)scaled;
    sink = (int)result;
    return result;
}

__attribute__((noinline))
unsigned mask_and_shift(unsigned x, signed char tag) {
    unsigned low = x & 0xffu;
    unsigned mid = (x >> 8) & 0xffu;
    unsigned top = (unsigned)tag & 0x80u;
    unsigned packed = (low << 2) | mid | top;
    usink = low;
    sink = (int)mid;
    lsink = (long)top;
    sink = (int)packed;
    return packed;
}

int main(void) {
    return signed_unsigned_compare(-1, 7u)
         + char_short_extensions(-3, 200u, -40, 1000u)
         + explicit_truncation(0x1234, 0xabcd)
         + boolean_normalization(5, 9)
         + (int)mixed_width_arithmetic(100000L, -17, 23u)
         + (int)mask_and_shift(0x1234u, -2);
}

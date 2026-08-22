/* A pointer is an integer-register value at cvtsi2sd, even when the same
 * incoming value is also proven pointer-shaped by a dereference. */

volatile unsigned char observed_byte;
volatile double observed_pointer_bits;
static unsigned char object;

__attribute__((noinline))
int record_pointer_bits(const unsigned char *ptr) {
    observed_byte = *ptr;
    observed_pointer_bits = (double)(long)ptr;
    return observed_byte;
}

int main(void) {
    return record_pointer_bits(&object);
}

/* A one-operand DIV/IDIV leaves the quotient in AX and the remainder in DX.  Each function below
   uses both, so neither result may be dropped, and the 64-bit forms divide the whole 64-bit
   dividend.  Divisors come from the caller's arguments so no constant reaches a division. */
#include <stddef.h>

__attribute__((noinline)) long sdiv64(long a, long b, long *rem) {
    *rem = a % b;
    return a / b;
}

__attribute__((noinline)) unsigned long udiv64(unsigned long a, unsigned long b, unsigned long *rem) {
    *rem = a % b;
    return a / b;
}

__attribute__((noinline)) int sdiv32(int a, int b, int *rem) {
    *rem = a % b;
    return a / b;
}

__attribute__((noinline)) unsigned udiv32(unsigned a, unsigned b, unsigned *rem) {
    *rem = a % b;
    return a / b;
}

__attribute__((noinline)) long srem64(long a, long b) {
    return a % b;
}

/* gnulib xpalloc's small-array path: the element count is the quotient of a constant byte size,
   and the remainder rounds the byte count down. */
__attribute__((noinline)) ptrdiff_t round_count(ptrdiff_t s, ptrdiff_t *nbytes) {
    ptrdiff_t adjusted = 128;
    *nbytes = adjusted - adjusted % s;
    return adjusted / s;
}

int main(int argc, char **argv) {
    long r;
    unsigned long ur;
    int ir;
    unsigned uir;
    ptrdiff_t nb;
    long q = sdiv64(0x123456789abL * argc, argc + 6, &r);
    unsigned long uq = udiv64(0xfedcba9876543210UL / argc, argc + 10, &ur);
    int iq = sdiv32(-1000003 * argc, argc + 16, &ir);
    unsigned uiq = udiv32(4000000000U / argc, argc + 6, &uir);
    ptrdiff_t n = round_count(16 * argc, &nb);
    return (int)(q + r + uq + ur + iq + ir + uiq + uir + srem64(q, argc + 1) + n + nb + (argv != 0)) & 1;
}

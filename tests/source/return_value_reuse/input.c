/* A returned value that a non-return instruction also reads.  At -O2 the
   compiler keeps memcpy's returned pointer in the ABI return register, stores
   through it, and returns it unchanged, so the register's definition has both a
   non-return consumer and the return.  gnulib's base_name() is this shape. */
#include <stdlib.h>
#include <string.h>

__attribute__((noinline))
char *dup_prefix(const char *s, unsigned long n) {
    char *p = malloc(n + 1);
    memcpy(p, s, n);
    p[n] = '\0';
    return p;
}

__attribute__((noinline))
int *fill_and_return(int *a, int n) {
    memset(a, 0, n * sizeof *a);
    a[0] = n;
    return a;
}

/* The branchless carry idioms: `sbb %r,%r` is -CF, not a subtraction, and a
   cmp/sbb $imm pair carries a residual constant past the carry. */
__attribute__((noinline))
long mask_of_lt(unsigned long a, unsigned long b) {
    return -(long)(a < b);
}

__attribute__((noinline))
int rank_of_cmp(const char *s) {
    return strcmp(s, "POSIX") == 0 ? 1 : 2;
}

__attribute__((noinline))
int nonzero_mask(unsigned x) {
    return -(int)(x != 0);
}

int main(int argc, char **argv) {
    char *p = dup_prefix(argc > 1 ? argv[1] : "hello world", 5);
    int buf[4];
    int *q = fill_and_return(buf, 4);
    long r = mask_of_lt((unsigned long)argc, 2);
    int k = rank_of_cmp(argc > 1 ? argv[1] : "C");
    int m = nonzero_mask((unsigned)argc - 1);
    int acc = (int)(p[0] + q[0] + r + k + m);
    free(p);
    return acc;
}

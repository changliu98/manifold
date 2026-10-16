/* PIE: passing an imported function as a value loads its address from the GOT
   (mov sym@GOTPCREL(%rip), %reg, a R_X86_64_GLOB_DAT slot). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void (*freer)(void *);
typedef int (*cmpfn)(const char *, const char *);

__attribute__((noinline)) void apply(freer f, void *p) { f(p); }
__attribute__((noinline)) int compare(cmpfn f, const char *a, const char *b) { return f(a, b); }

int main(int argc, char **argv) {
    void *p = malloc(16);
    apply(free, p);
    cmpfn cmp = argc > 1 ? strcmp : strcoll;
    printf("%d\n", compare(cmp, argv[0], "x") > 0);
    return 0;
}

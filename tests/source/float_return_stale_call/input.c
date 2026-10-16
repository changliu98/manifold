/* gnulib's c_strtod: a double-returning function whose only AX values are a cached
   locale_t (a newlocale() result) that still sits in RAX on the `return 0` path. */
#define _GNU_SOURCE
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>

static locale_t c_locale_cache;

__attribute__((noinline)) double c_strtod(const char *nptr, char **endptr) {
    if (!c_locale_cache)
        c_locale_cache = newlocale(LC_ALL_MASK, "C", (locale_t)0);
    if (!c_locale_cache) {
        if (endptr)
            *endptr = (char *)nptr;
        return 0;
    }
    return strtod_l(nptr, endptr, c_locale_cache);
}

int main(int argc, char **argv) {
    char *end;
    double v = c_strtod(argc > 1 ? argv[1] : "2.5", &end);
    printf("%g\n", v * 2);
    return 0;
}

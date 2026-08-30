#include <stdlib.h>
#include <string.h>

/* These wrappers must remain ordinary known-external tail calls.  The
 * manifest disables builtins so neither compiler substitutes local logic. */
__attribute__((noinline))
long frontier_tail_labs(long value) {
    return labs(value);
}

__attribute__((noinline))
char *frontier_tail_strchr(const char *text, int needle) {
    return strchr(text, needle);
}

int main(int argc, char **argv) {
    if (argc < 4) {
        return 2;
    }
    const char *text = argv[1];
    int needle = (unsigned char)argv[2][0];
    long signed_value = (long)(unsigned char)argv[3][0] * 7L - 500L;

    long magnitude = frontier_tail_labs(signed_value);
    char *found = frontier_tail_strchr(text, needle);
    unsigned pointer_digest = found
        ? (unsigned)(found - text) * 17U + (unsigned char)*found
        : 97U;
    return (int)(((unsigned long)(magnitude * 3L) + pointer_digest) & 255UL);
}

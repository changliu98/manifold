/* gnulib force_symlinkat: a name is built in a 256-byte local buffer when it fits and in heap
   storage otherwise, and the chosen storage is filled by a callee.  The buffer's address only may
   reach the call, through the join with malloc, yet the callee can write all of it. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__attribute__((noinline)) int fill(char *dst, const char *src, size_t n) {
    memcpy(dst, src, n);
    memcpy(dst + n, ".tmp", 5);
    return (int)n;
}

__attribute__((noinline)) int with_temp_name(const char *name) {
    char buf[256];
    size_t len = strlen(name);
    char *tmp = len + 5 <= sizeof buf ? buf : malloc(len + 5);
    if (!tmp)
        return -1;
    fill(tmp, name, len);
    int r = puts(tmp);
    if (tmp != buf)
        free(tmp);
    return r;
}

int main(int argc, char **argv) {
    return with_temp_name(argc > 1 ? argv[1] : "name") < 0;
}

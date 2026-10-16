/* ln's main: an option switch dispatched through a jump table, then a loop passing a local's
   address to a callee that stores through it and reading the local back.  The dispatch's targets
   are all recovered, so the function's control is closed and the local must stay one object. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__attribute__((noinline)) char *concat(const char *dir, const char *base, char **base_in_result) {
    size_t dl = strlen(dir), bl = strlen(base);
    char *p = malloc(dl + bl + 2);
    memcpy(p, dir, dl);
    p[dl] = '/';
    memcpy(p + dl + 1, base, bl + 1);
    if (base_in_result)
        *base_in_result = p + dl + 1;
    return p;
}

__attribute__((noinline)) void strip(char *s) {
    size_t n = strlen(s);
    while (n > 1 && s[n - 1] == '/')
        s[--n] = 0;
}

__attribute__((noinline)) int use(const char *a, const char *b) {
    return printf("%s %s\n", a, b) > 0;
}

int flags[8];

int main(int argc, char **argv) {
    int ok = 1, i = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        switch (argv[i][1]) {
        case 'a': flags[0]++; break;
        case 'b': flags[1]++; break;
        case 'c': flags[2]++; break;
        case 'd': flags[3]++; break;
        case 'e': flags[4]++; break;
        case 'f': flags[5]++; break;
        case 'g': flags[6] = 3; break;
        default: flags[7]--; break;
        }
    }
    for (; i < argc; i++) {
        char *base;
        char *d = concat("/tmp", argv[i], &base);
        strip(base);
        ok &= use(base, d);
        free(d);
    }
    return !ok + flags[7];
}

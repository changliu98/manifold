#include <stdint.h>

__attribute__((noinline))
static int mutate(int *primary, int *alias, int delta) {
    *primary += delta;
    int observed = *alias;
    *alias = observed ^ (delta * 9 + 3);
    return *primary + 3 * *alias + 5 * observed;
}

int main(int argc, char **argv) {
    (void)argv;
    int slots[3] = {11, 23, 37};
    unsigned index = (unsigned)(argc - 1) % 3u;
    int first = mutate(&slots[1], &slots[index], argc + 2);
    int second = mutate(&slots[1], &slots[1], argc + 5);
    return (first + second + slots[0] + 3 * slots[1] + 7 * slots[2]) & 255;
}

#define _FILE_OFFSET_BITS 64
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

/* A string examined at constant offsets and handed to a C library function
 * whose contract names `const char *` is a character pointer, not a record. */
__attribute__((noinline)) int option_kind(const char *text) {
    if (text[0] == '-' && text[1] == '-')
        return strcmp(text + 2, "help") == 0 ? 2 : 1;
    return text[1] == 'v';
}

/* Only the format string names these variadic argument types. */
__attribute__((noinline)) void report(const char *name, long count) {
    fprintf(stderr, "%s: %ld\n", name, count);
}

/* Large-file symbols (open64/fstat64/mmap64) have their base functions'
 * prototypes; the mapping must stay a full-width pointer. */
__attribute__((noinline)) long first_byte(const char *path) {
    int fd = open(path, O_RDONLY);
    if (fd < 0)
        return -1;
    struct stat st;
    if (fstat(fd, &st) < 0 || st.st_size == 0) {
        close(fd);
        return -2;
    }
    unsigned char *map = mmap(0, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (map == MAP_FAILED)
        return -3;
    long value = map[0];
    munmap(map, st.st_size);
    return value;
}

struct pair {
    int key;
    long value;
    char tag;
};

/* A heterogeneous record layout keeps its identity. */
__attribute__((noinline)) long pair_value(struct pair *p) {
    return p->value + p->key + p->tag;
}

int main(int argc, char **argv) {
    struct pair p = {1, 2, 3};
    report(argv[0], pair_value(&p));
    printf("%ld\n", first_byte(argv[0]));
    return option_kind(argc > 1 ? argv[1] : "--help");
}

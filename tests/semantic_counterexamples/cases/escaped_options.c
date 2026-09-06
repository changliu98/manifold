#include <stdint.h>
#ifdef GETOPT_OPTIONS
#include <unistd.h>
#endif

struct Options {
    unsigned char ignore_missing;
    unsigned mode;
    unsigned char recursive;
    uint64_t limit;
#ifdef FLOAT_OPTIONS
    double weight;
#endif
    unsigned char verbose;
};

__attribute__((noinline))
static unsigned inspect_options(const struct Options *options)
{
    __asm__ volatile ("" : : "r" (options) : "memory");
    return options->mode * 7u + options->recursive * 13u
#ifdef FLOAT_OPTIONS
        + (unsigned) (options->weight * 8.0)
#endif
        + (unsigned) options->limit + options->ignore_missing
        + options->verbose * 3u;
}

int main(int argc, char **argv)
{
    (void) argv;
    struct Options options;
    options.ignore_missing = 0;
    options.mode = 4;
    options.recursive = argc & 1;
    options.limit = 19u + (unsigned) argc;
#ifdef FLOAT_OPTIONS
    options.weight = (double) argc + 0.5;
#endif
    options.verbose = 0;
#ifdef GETOPT_OPTIONS
    int option;
    while ((option = getopt(argc, argv, "bimrlv")) != -1) {
        switch (option) {
        case 'b': options.mode = 13; break;
        case 'i': options.ignore_missing = 1; break;
        case 'm': options.mode = 6; break;
        case 'r': options.recursive = 1; break;
        case 'l': options.limit += 8; break;
        case 'v': options.verbose = 2; break;
        default: return 200;
        }
    }
#endif
#ifdef SWITCH_OPTIONS
    switch (argc & 7) {
    case 0: options.mode = 13; break;
    case 1: options.ignore_missing = 1; break;
    case 2: options.recursive = 1; break;
    case 3: options.limit += 8; break;
    case 4: options.verbose = 1; break;
    case 5: options.mode = 6; break;
    case 6: options.ignore_missing = 1; options.verbose = 2; break;
    default: options.limit = 5; break;
    }
#endif
    return inspect_options(&options) & 255u;
}

#include <stdarg.h>

__attribute__((noinline))
static unsigned sum_args(unsigned count, ...)
{
    va_list arguments;
    va_start(arguments, count);
    unsigned total = 0;
    for (unsigned i = 0; i < count; ++i)
        total += va_arg(arguments, unsigned);
    va_end(arguments);
    return total;
}

int main(int argc, char **argv)
{
    (void) argv;
    return sum_args((unsigned) argc % 3u + 1u, 3u, 5u, 7u);
}

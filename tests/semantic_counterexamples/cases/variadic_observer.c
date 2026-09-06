#include <stdarg.h>
#include <stdio.h>

__attribute__((noinline, format(printf, 1, 2)))
static void report(const char *format, ...)
{
    va_list arguments;
    va_start(arguments, format);
#if defined(USE_DESCRIPTOR)
    vdprintf(1, format, arguments);
#else
    vfprintf(stdout, format, arguments);
#endif
    va_end(arguments);
}

int main(int argc, char **argv)
{
    (void) argv;
    report("entry=%s count=%d value=%.2f\n", "payload", argc, 7.25);
    return 0;
}

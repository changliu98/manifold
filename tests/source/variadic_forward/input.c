#include <stdarg.h>

typedef long (*va_consumer)(va_list *);

__attribute__((noinline))
long consume_one_long(va_list *args) {
    return va_arg(*args, long);
}

/* Keep the consumer opaque to the variadic function.  That forces both GCC
 * and Clang to materialize the complete SysV va_list register-save area
 * instead of specializing the prologue for one known va_arg type. */
volatile va_consumer selected_consumer = consume_one_long;

__attribute__((noinline))
long forward_variadic(
    long a0,
    long a1,
    long a2,
    long a3,
    long a4,
    long a5,
    void *last_named,
    ...
) {
    va_list args;
    va_start(args, last_named);
    long value = selected_consumer(&args);
    va_end(args);
    return value + (a0 - a1) + (a2 - a3) + (a4 - a5);
}

int main(void) {
    return forward_variadic(1, 1, 2, 2, 3, 3, 0, 37L) != 37L;
}

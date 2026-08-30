#include <stdarg.h>
#include <stdint.h>

typedef long (*frontier_va_consumer)(va_list *);

/* Fetch in declaration order so the GP and XMM cursors advance independently.
 * The final two longs and final two doubles come from the overflow area. */
__attribute__((noinline))
long frontier_consume_mixed(va_list *args) {
    long total = 0;

    total += va_arg(*args, long) * 3;
    total += (long)(va_arg(*args, double) * 8.0) * 5;
    total += va_arg(*args, long) * 7;
    total += (long)(va_arg(*args, double) * 8.0) * 11;
    total += va_arg(*args, long) * 13;
    total += (long)(va_arg(*args, double) * 8.0) * 17;
    total += va_arg(*args, long) * 19;
    total += (long)(va_arg(*args, double) * 8.0) * 23;
    total += va_arg(*args, long) * 29;
    total += (long)(va_arg(*args, double) * 8.0) * 31;
    total += va_arg(*args, long) * 37;
    total += (long)(va_arg(*args, double) * 8.0) * 41;
    total += va_arg(*args, long) * 43;
    total += (long)(va_arg(*args, double) * 8.0) * 47;
    total += (long)(va_arg(*args, double) * 8.0) * 53;
    total += (long)(va_arg(*args, double) * 8.0) * 59;
    total += (long)(va_arg(*args, double) * 8.0) * 61;

    return total;
}

/* A volatile function pointer prevents either compiler from specializing the
 * va_list layout for a visible consumer. */
volatile frontier_va_consumer frontier_selected_consumer =
    frontier_consume_mixed;

__attribute__((noinline))
unsigned long frontier_mixed_variadic(unsigned long seed, ...) {
    va_list args;
    va_list copied;
    va_start(args, seed);
    va_copy(copied, args);

    frontier_va_consumer consumer = frontier_selected_consumer;
    long first = consumer(&args);
    long second = consumer(&copied);

    va_end(copied);
    va_end(args);
    return seed + (unsigned long)first + 3UL * (unsigned long)second;
}

typedef unsigned long (*frontier_variadic_entry)(unsigned long, ...);
volatile frontier_variadic_entry frontier_selected_entry =
    frontier_mixed_variadic;

int main(int argc, char **argv) {
    (void)argv;
    long t = argc;
    frontier_variadic_entry entry = frontier_selected_entry;
    unsigned long digest = entry(
        (unsigned long)(97 + 13 * t),
        11L + t, 1.25 + (double)t,
        22L - t, -2.5 - (double)t,
        33L + 2 * t, 3.75 + 0.5 * (double)t,
        44L - 3 * t, 4.5 - 0.25 * (double)t,
        55L + 4 * t, -5.25 + 0.75 * (double)t,
        66L - 5 * t, 6.0 - 0.5 * (double)t,
        77L + 6 * t, 7.125 + 0.125 * (double)t,
        8.25 - 0.25 * (double)t,
        -9.5 + 0.5 * (double)t,
        10.75 - 0.75 * (double)t);
    return (int)(digest & 255UL);
}

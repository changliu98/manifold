__attribute__((noinline))
static unsigned window(unsigned value, unsigned char *p)
{
    p[0] = value;
    p[32] = value + 1;
    __asm__ volatile ("" : : "r" (p) : "memory");
    return p[0] ^ p[32];
}

int main(int argc, char **argv)
{
    (void) argv;
    unsigned char bytes[64];
    return window((unsigned) argc, bytes + ((unsigned) argc & 7u));
}

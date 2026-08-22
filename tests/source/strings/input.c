/* strings: string operation patterns.
 * Inspired by angr's test_decompiling_strings_local_strlen/strcat
 * and string literal recovery tests. */

volatile int sink;

__attribute__((noinline))
int my_strlen(const char *s) {
    int len = 0;
    while (s[len] != '\0') {
        len++;
    }
    return len;
}

__attribute__((noinline))
int my_strcmp(const char *a, const char *b) {
    while (*a && *a == *b) {
        a++;
        b++;
    }
    return *a - *b;
}

__attribute__((noinline))
int count_char(const char *s, char c) {
    int count = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        if (s[i] == c) {
            count++;
        }
    }
    return count;
}

__attribute__((noinline))
void reverse_inplace(char *s) {
    int len = my_strlen(s);
    for (int i = 0; i < len / 2; i++) {
        char tmp = s[i];
        s[i] = s[len - 1 - i];
        s[len - 1 - i] = tmp;
    }
}

__attribute__((noinline))
int string_search(const char *haystack, const char *needle) {
    int hlen = my_strlen(haystack);
    int nlen = my_strlen(needle);
    if (nlen > hlen) return -1;
    for (int i = 0; i <= hlen - nlen; i++) {
        int match = 1;
        for (int j = 0; j < nlen; j++) {
            if (haystack[i + j] != needle[j]) {
                match = 0;
                break;
            }
        }
        if (match) return i;
    }
    return -1;
}

__attribute__((noinline))
int use_string_literal(int x) {
    const char *msg = "hello world";
    sink = msg[0];
    if (x > 0) {
        return my_strlen(msg);
    }
    return my_strlen("goodbye");
}

__attribute__((noinline))
void my_strcpy(char *dst, const char *src) {
    while ((*dst++ = *src++) != '\0')
        ;
}

int main(void) {
    char buf[64] = "hello world";
    reverse_inplace(buf);
    return my_strlen(buf) + my_strcmp("abc", "abd")
         + count_char(buf, 'l')
         + string_search(buf, "llo")
         + use_string_literal(1);
}

#include <ctype.h>
#include <malloc.h>
#include <stdlib.h>
#include <string.h>

/* At -O0 `rows[i][keys[i - 1]]` computes &keys[i - 1], loads the key and
 * scales it into the next address in ONE machine register: an address, an
 * element value and an address again.  Recovering it must keep every address
 * full width however that register's C variable is typed, in a function large
 * enough that its semantic checks cannot all be exhaustively proved. */
__attribute__((noinline)) int tally(int n) {
    int *keys = malloc(n * sizeof(int));
    int **rows = malloc((n + 1) * sizeof(int *));
    int **scratch = malloc((n + 1) * sizeof(int *));
    for (int i = 0; i <= n; i++) {
        rows[i] = calloc(3, sizeof(int));
        scratch[i] = calloc(3, sizeof(int));
    }
    rows[0][0] = rows[0][1] = rows[0][2] = 0;
    scratch[0][0] = scratch[0][1] = scratch[0][2] = 0;
    for (int i = 1; i <= n; i++) {
        keys[i - 1] = (i * i - i + 1) % 3;
        for (int j = 0; j < 3; j++)
            rows[i][j] = rows[i - 1][j];
        rows[i][keys[i - 1]] += 1;
    }
    for (int round = 1; round < 3; round++) {
        for (int i = 1; i <= n; i++) {
            for (int j = 0; j < 3; j++)
                scratch[i][j] = scratch[i - 1][j];
            for (int j = 0; j <= 2; j++)
                scratch[i][(keys[i - 1] + j) % 3] += rows[i - 1][j];
        }
        for (int i = 0; i <= n; i++) {
            for (int j = 0; j < 3; j++) {
                rows[i][j] = scratch[i][j];
                scratch[i][j] = 0;
            }
        }
    }
    int result = rows[n][0];
    for (int i = 0; i <= n; ++i) {
        free(rows[i]);
        free(scratch[i]);
    }
    free(rows);
    free(scratch);
    free(keys);
    return result;
}

/* Words of `s` with exactly `n` consonants.  The ctype table lookups reuse one
 * register for the character and for the table address it indexes. */
__attribute__((noinline)) char **pick_words(const char *s, int n, int *count) {
    const char *vowels = "aeiouAEIOU";
    char **out = NULL;
    int consonants = 0, words = 0, begin = 0;
    size_t length = strlen(s);
    char *current = malloc(length + 1);
    for (size_t i = 0; i <= length; i++) {
        if (isspace((unsigned char)s[i]) || s[i] == '\0') {
            if (consonants == n) {
                current[i - begin] = '\0';
                out = realloc(out, sizeof(char *) * (words + 1));
                out[words] = malloc(strlen(current) + 1);
                strcpy(out[words], current);
                words++;
            }
            begin = i + 1;
            consonants = 0;
        } else {
            current[i - begin] = s[i];
            if (strchr(vowels, s[i]) == NULL && isalpha((unsigned char)s[i]))
                consonants++;
        }
    }
    free(current);
    *count = words;
    return out;
}

int main(void) {
    int count = 0;
    char **words = pick_words("Mary had a little lamb", 4, &count);
    int ok = tally(10) == 36 && count == 1 && strcmp(words[0], "little") == 0;
    return ok ? 0 : 1;
}

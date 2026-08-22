/* memory_layout: memory addressing and aggregate layout coverage. */

volatile int sink;
volatile unsigned int usink;

int global_grid[3][4] = {
    {1, 2, 3, 4},
    {5, 6, 7, 8},
    {9, 10, 11, 12},
};

struct Bucket {
    int slots[3];
};

struct Bucket global_buckets[2] = {
    {{13, 14, 15}},
    {{16, 17, 18}},
};

struct Record {
    unsigned char tag;
    unsigned short count;
    int value;
};

__attribute__((noinline))
int multidim_index(int row, int col) {
    int a = global_grid[row][col];
    int b = global_grid[(row + 1) % 3][(col + 2) % 4];
    sink = a;
    return a + b;
}

__attribute__((noinline))
int nested_global_index(int bucket, int slot) {
    int a = global_buckets[bucket].slots[slot];
    int b = global_buckets[(bucket + 1) & 1].slots[(slot + 1) % 3];
    sink = b;
    return a - b;
}

__attribute__((noinline))
int pointer_to_pointer_walk(int **rows, int n) {
    int total = 0;
    for (int i = 0; i < n; i++) {
        int *row = rows[i];
        total += row[0] + row[1];
    }
    sink = total;
    return total;
}

__attribute__((noinline))
int struct_array_offsets(struct Record *records, int n) {
    int total = 0;
    for (int i = 0; i < n; i++) {
        total += records[i].tag;
        total += records[i].count;
        total += records[i].value;
    }
    sink = total;
    return total;
}

__attribute__((noinline))
int local_aggregate_use(int x) {
    struct Record records[2] = {
        {(unsigned char)(x + 1), (unsigned short)(x + 2), x + 3},
        {(unsigned char)(x + 4), (unsigned short)(x + 5), x + 6},
    };
    int local_grid[2][3] = {
        {x, x + 1, x + 2},
        {x + 3, x + 4, x + 5},
    };
    int result = records[0].tag + records[1].count;
    result += records[1].value + local_grid[1][2];
    sink = result;
    return result;
}

__attribute__((noinline))
unsigned int byte_word_access(unsigned char *bytes, unsigned short *words, int idx) {
    unsigned int b = bytes[idx];
    unsigned int w = words[idx + 1];
    bytes[idx] = (unsigned char)(b + 1);
    words[idx + 1] = (unsigned short)(w + b);
    usink = b + w;
    return bytes[idx] + words[idx + 1];
}

int main(void) {
    int row0[2] = {1, 2};
    int row1[2] = {3, 4};
    int *rows[2] = {row0, row1};
    struct Record records[2] = {
        {1, 20, 300},
        {2, 30, 400},
    };
    unsigned char bytes[4] = {10, 20, 30, 40};
    unsigned short words[4] = {100, 200, 300, 400};

    return multidim_index(1, 2)
         + nested_global_index(0, 1)
         + pointer_to_pointer_walk(rows, 2)
         + struct_array_offsets(records, 2)
         + local_aggregate_use(5)
         + (int)byte_word_access(bytes, words, 1);
}

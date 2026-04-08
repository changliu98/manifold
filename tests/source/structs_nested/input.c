/* structs_nested: deep struct access patterns.
 * Inspired by angr's test_struct_access which validates
 * nested field chains like c_ptr->c2[argc].b2.a2. */

volatile int sink;

struct Inner {
    int x;
    int y;
};

struct Middle {
    struct Inner a;
    struct Inner b;
    int tag;
};

struct Outer {
    struct Middle items[4];
    int count;
    struct Inner *extra;
};

struct Node {
    int value;
    struct Node *next;
};

__attribute__((noinline))
int read_nested(struct Outer *o, int idx) {
    return o->items[idx].a.x + o->items[idx].b.y;
}

__attribute__((noinline))
void write_nested(struct Outer *o, int idx, int val) {
    o->items[idx].a.x = val;
    o->items[idx].a.y = val + 1;
    o->items[idx].b.x = val + 2;
    o->items[idx].b.y = val + 3;
    o->items[idx].tag = val * 2;
    sink = o->items[idx].tag;
}

__attribute__((noinline))
int array_of_structs_sum(struct Inner *arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        sum += arr[i].x + arr[i].y;
    }
    return sum;
}

__attribute__((noinline))
int linked_list_sum(struct Node *head) {
    int sum = 0;
    struct Node *cur = head;
    while (cur != 0) {
        sum += cur->value;
        cur = cur->next;
    }
    return sum;
}

__attribute__((noinline))
int linked_list_length(struct Node *head) {
    int len = 0;
    for (struct Node *p = head; p != 0; p = p->next) {
        len++;
    }
    return len;
}

__attribute__((noinline))
int struct_chain_access(struct Outer *o) {
    /* Access through extra pointer and direct nested */
    int a = o->extra->x;
    int b = o->extra->y;
    int c = o->items[0].a.x;
    int d = o->count;
    return a + b + c + d;
}

__attribute__((noinline))
int modify_through_pointer(struct Inner *p) {
    p->x += 10;
    p->y *= 2;
    sink = p->x + p->y;
    return p->x - p->y;
}

int main(void) {
    struct Inner arr[3] = {{1, 2}, {3, 4}, {5, 6}};
    struct Node n3 = {30, 0};
    struct Node n2 = {20, &n3};
    struct Node n1 = {10, &n2};
    struct Outer o;
    o.count = 4;
    o.extra = &arr[0];
    write_nested(&o, 0, 100);
    return read_nested(&o, 0) + array_of_structs_sum(arr, 3)
         + linked_list_sum(&n1) + linked_list_length(&n1)
         + struct_chain_access(&o) + modify_through_pointer(&arr[1]);
}

// A byte flag living in a frame slot, assigned on several paths and then
// compared against zero.  The slot's reads have more than one reaching
// definition, so the initializer is not the slot's value at the test; a
// recovered condition of the form `0 != 0` means a definition was lost and
// the surviving one was substituted into every read.
//
// The tail also mirrors a branch whose two arms leave to different joins with
// a third section printed between the compound and its join, which is the
// layout where an elided arm edge falls into the wrong section.

volatile int sink;

__attribute__((noinline))
int next_opt(int i)
{
    sink = i;
    return (i * 7) % 5;
}

__attribute__((noinline))
void warn_same(void)
{
    sink = 2;
}

__attribute__((noinline))
void warn_conflict(long depth)
{
    sink = (int)depth + 1;
}

__attribute__((noinline))
int summarize_flag_conflict(int n)
{
    char summarize = 0;
    char apparent = 0;
    long max_depth = -1;

    for (int i = 0; i < n; i++) {
        switch (next_opt(i)) {
        case 0:
            summarize = 1;
            break;
        case 1:
            max_depth = i;
            break;
        case 2:
            apparent = 1;
            break;
        case 3:
            max_depth = 0;
            break;
        default:
            summarize = 0;
            break;
        }
    }

    if (summarize) {
        if (max_depth == 0) {
            warn_same();
        } else if (max_depth > 0) {
            warn_conflict(max_depth);
            return 1;
        }
        max_depth = 0;
    }

    if (apparent) {
        sink = 5;
        return 2;
    }
    return (int)max_depth;
}

int main(void)
{
    return summarize_flag_conflict(6);
}

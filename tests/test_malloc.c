#include <stdlib.h>

/* A client of malloc and free only. The claim about it: every run that
   exits does so with 0, or 1 when memory runs out -- never 42, which it
   returns when a block's bytes changed under it (the allocator wrote
   into a live block, or handed out overlapping blocks). It may also die
   of a stack overflow; no other crash. */

#define N 8

/* (an int: C1 has no narrow return values yet) */
static int pat(int i, int j) { return (31 * i + j) & 255; }

static int size(int i) { return 16 + 40 * i; }

/* the block's bytes still its pattern */
static int intact(unsigned char *b, int i) {
    for (int j = 0; j < size(i); j++)
        if (b[j] != pat(i, j)) return 0;
    return 1;
}

static void fill(unsigned char *b, int i) {
    for (int j = 0; j < size(i); j++) b[j] = pat(i, j);
}

int main(void) {
    unsigned char *p[N];
    for (int i = 0; i < N; i++) {
        p[i] = malloc(size(i));
        if (!p[i]) return 1;
        fill(p[i], i);
    }
    /* free every other block, allocate them again: the others kept */
    for (int i = 0; i < N; i += 2) free(p[i]);
    for (int i = 0; i < N; i += 2) {
        p[i] = malloc(size(i));
        if (!p[i]) return 1;
        fill(p[i], i);
    }
    for (int i = 0; i < N; i++)
        if (!intact(p[i], i)) return 42;
    for (int i = 0; i < N; i++) free(p[i]);
    return 0;
}

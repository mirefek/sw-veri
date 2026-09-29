/* A random mix of malloc, calloc and free, for checking the allocator
 * invariant on real heaps (`slc heapcheck`). Sizes cover tiny, small and
 * medium size classes and the individually mapped blocks above
 * MMAP_THRESHOLD; every block is written like a client would. */
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static unsigned long long s = 88172645463325252ull;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

#define MAXN 8192
static void *ptr[MAXN];
static int N = 256;                             /* live pointers at most (argv[3]) */

static size_t pick_size(void) {
    unsigned r = rnd() % 100;
    if (r < 40) return rnd() % 64;              /* tiny, including 0 */
    if (r < 75) return rnd() % 1024;
    if (r < 95) return rnd() % 20000;
    return 100000 + rnd() % 200000;             /* around and above MMAP_THRESHOLD */
}

int main(int argc, char **argv) {
    int steps = argc > 1 ? atoi(argv[1]) : 2000;
    if (argc > 2) s += (unsigned long long)atoi(argv[2]);
    if (argc > 3) N = atoi(argv[3]) < MAXN ? atoi(argv[3]) : MAXN;
    /* argv[4] = 1: the client maps its own memory just above the break, so
     * the allocator's brk fails and it takes its metadata areas from mmap */
    if (argc > 4 && atoi(argv[4])) {
        char *b = sbrk(0);
        b += -(unsigned long)b & 4095;
        (void)mmap(b, 4 * 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    }
    for (int t = 0; t < steps; t++) {
        int i = rnd() % N;
        if (ptr[i]) {
            free(ptr[i]);
            ptr[i] = 0;
        } else {
            size_t n = pick_size(), total = n;
            if (rnd() % 4 == 0) {
                size_t m = 1 + rnd() % 8;
                total = m * (n / m + 1);
                ptr[i] = calloc(m, n / m + 1);
            } else {
                ptr[i] = malloc(n);
            }
            if (ptr[i]) memset(ptr[i], t & 0xff, total);
        }
    }
    free(0);
    return 0;
}

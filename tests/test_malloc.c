#include <stdlib.h>
#include <string.h>

/* Keeps malloc/free/calloc linked and called; the claim is about them. */
int main(int argc, char **argv) {
    (void)argv;
    char *p = malloc(100 + argc);
    if (!p) return 1;
    memset(p, 'x', 100);
    int *q = calloc(10, sizeof(int));
    int r = p[argc] + (q ? q[argc] : 0);
    free(p);
    free(q);
    return r == 'x' ? 0 : 2;
}

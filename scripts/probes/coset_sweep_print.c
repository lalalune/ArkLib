#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static int N, HALF, NCLS, TARGET;
static int subs[5][20][4], subcnt[5];
static int elems[64];
static void check(int nel) {
    int fold[64];
    memset(fold, 0, sizeof(int) * HALF);
    for (int i = 0; i < nel; i++)
        for (int j = i + 1; j < nel; j++) {
            int s = (elems[i] + elems[j]) % N;
            if (s < HALF) fold[s]++; else fold[s - HALF]--;
        }
    for (int t = 0; t < HALF; t++) if (fold[t]) return;
    for (int i = 0; i < nel; i++) printf("%d ", elems[i]);
    printf("\n");
}
static void dfs(int cls, int rem, int nel) {
    if (cls == NCLS) { if (rem == 0) check(nel); return; }
    int maxs = rem < 3 ? rem : 3;
    for (int s = 0; s <= maxs; s++) {
        if (rem - s > 3 * (NCLS - cls - 1)) continue;
        for (int c = 0; c < subcnt[s]; c++) {
            for (int e = 0; e < s; e++) elems[nel + e] = cls + NCLS * subs[s][c][e];
            dfs(cls + 1, rem - s, nel + s);
        }
    }
}
int main(int argc, char **argv) {
    N = atoi(argv[1]); TARGET = atoi(argv[2]); HALF = N/2; NCLS = N/4;
    for (int s = 0; s <= 3; s++) subcnt[s] = 0;
    for (int mask = 0; mask < 16; mask++) {
        int bits = __builtin_popcount(mask);
        if (bits > 3) continue;
        int k = 0;
        for (int b = 0; b < 4; b++) if (mask & (1<<b)) subs[bits][subcnt[bits]][k++] = b;
        subcnt[bits]++;
    }
    dfs(0, TARGET, 0);
    return 0;
}

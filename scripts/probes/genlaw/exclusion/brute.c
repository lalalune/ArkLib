/* brute.c — INDEPENDENT checker: raw feasibility by direct enumeration of ALL
 * B-subsets (no axis logic, no forced/free analysis, no DP).
 * For each O-set (r distinct fibers in Z_s) and each sign class m (m_1=0):
 *   for every B subset of (Z_s \ O) with |B| = b = (s+1-r)/2:
 *     build the full multiset cnt[] over Z_2s:
 *       products (a_i+a_j), O-doubles 2*o_i, B-doubles 2*f, lambda 3s/2
 *     feasible iff cnt[t] == cnt[t+s] for ALL t in [0,s).
 *   ways(O,m) = number of feasible B.
 * Prints per-class records "REC o1..or | m | w" and totals.
 * args: s r
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, N, R, Bsz;
static long long nclasses = 0, waysum = 0;
static int O[32];

static int comp[40], M;   /* complement fibers */
static int bidx[40];

static long long count_B(int *base) {
    /* enumerate B = b-subsets of comp[0..M-1]; cnt base given (non-B terms) */
    long long ways = 0;
    if (Bsz > M) return 0;
    for (int i = 0; i < Bsz; i++) bidx[i] = i;
    while (1) {
        int cnt[600];
        memcpy(cnt, base, sizeof(int) * N);
        for (int i = 0; i < Bsz; i++) cnt[(2 * comp[bidx[i]]) % N]++;
        int ok = 1;
        for (int t = 0; t < S && ok; t++)
            if (cnt[t] != cnt[t + S]) ok = 0;
        ways += ok;
        /* next combination */
        int i = Bsz - 1;
        while (i >= 0 && bidx[i] == M - Bsz + i) i--;
        if (i < 0) break;
        bidx[i]++;
        for (int j = i + 1; j < Bsz; j++) bidx[j] = bidx[j - 1] + 1;
    }
    return ways;
}

static void process(void) {
    M = 0;
    int ino[64];
    memset(ino, 0, sizeof ino);
    for (int i = 0; i < R; i++) ino[O[i]] = 1;
    for (int f = 0; f < S; f++) if (!ino[f]) comp[M++] = f;
    for (long m = 0; m < (1L << (R - 1)); m++) {
        int a[32];
        a[0] = O[0];
        for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
        int base[600];
        memset(base, 0, sizeof(int) * N);
        for (int i = 0; i < R; i++)
            for (int j = i + 1; j < R; j++)
                base[(a[i] + a[j]) % N]++;
        for (int i = 0; i < R; i++) base[(2 * O[i]) % N]++;
        base[(3 * S / 2) % N]++;
        long long w = count_B(base);
        if (w > 0) {
            nclasses++;
            waysum += w;
            printf("REC");
            for (int i = 0; i < R; i++) printf(" %d", O[i]);
            printf(" | m %ld | w %lld\n", m, w);
        }
    }
}

static void rec(int depth, int start) {
    if (depth == R) { process(); return; }
    for (int x = start; x < S; x++) { O[depth] = x; rec(depth + 1, x + 1); }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    N = 2 * S; Bsz = (S + 1 - R) / 2;
    rec(0, 0);
    printf("BRUTE TOTAL s %d r %d b %d classes %lld waysum %lld\n",
           S, R, Bsz, nclasses, waysum);
    return 0;
}

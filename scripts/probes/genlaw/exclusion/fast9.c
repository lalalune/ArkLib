/* fast9.c — Gray-code incremental pure-only death-census kernel.
 * Same criterion and gate ORDER as diag.c (G2 |d|>=2 -> G3 blocked ->
 * G4 h>b -> G5 parity -> G6 v-cap -> feasible, ways = C(v,(b-h)/2)),
 * pure parity classes only (justified by T1: all mixed die at G1).
 * Incremental state across the 2^(r-1) sign classes in Gray order:
 *   d[c] per axis, h = sum|d|, nbad = #axes |d|>=2.
 * Flipping sign bit i toggles the side of the r-1 products (i,j) only
 * (doubles and lambda are sign-independent). Slow path (axis scan for
 * blocking/free axes) only when nbad == 0.
 * args: s r [NW WID]   (worker stride over O-sets, same order as diag.c
 *                       pure mode: PAR=0 pass then PAR=1 pass, ocount
 *                       reset between passes)
 * Output: same DIAG lines as diag.c (minus dhist; minD == min h overall
 * since in pure mode every config passes G1).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, N, A, R, Bsz;
static long NW = 1, WID = 0;
static long long ocount = 0;
static int O[32], U[32], PAR = 0;

static long long c_pure = 0;
static long long die_d2 = 0, die_blocked = 0, die_hgtb = 0, die_par = 0, die_v = 0;
static long long feas = 0, waysum = 0;
static long long hhist[200];
static int minD = 1 << 30, minD_clean = 1 << 30;
static long long binom[80][80];

/* per-pair data, indexed [i][j] i<j */
static int axis_[32][32];   /* axis of product (i,j) */
static int contrib[32][32]; /* current +-1 contribution to d[axis] */
static int d[64], h_, nbad;

static inline void move_term(int c, int delta2) {
    /* term on axis c flips side: d[c] += delta2 (delta2 = +-2) */
    int od = d[c], nd = od + delta2;
    d[c] = nd;
    int aod = od < 0 ? -od : od, and_ = nd < 0 ? -nd : nd;
    h_ += and_ - aod;
    nbad += (and_ >= 2) - (aod >= 2);
}

static unsigned long long omask;

static void tally(void) {
    c_pure++;
    if (h_ < minD) minD = h_;
    if (nbad) { die_d2++; return; }
    /* slow path: blocking + free axes */
    int blocked = 0, v = 0;
    for (int c = 0; c < A; c++) {
        if (d[c] == 1 || d[c] == -1) {
            int ff = (d[c] == -1) ? c : c + A;
            if (omask & (1ULL << ff)) blocked++;
        } else if (d[c] == 0) {
            if (!(omask & (1ULL << c)) && !(omask & (1ULL << (c + A)))) v++;
        }
    }
    if (blocked) { die_blocked++; return; }
    if (h_ < minD_clean) minD_clean = h_;
    if (h_ > Bsz) { die_hgtb++; return; }
    if ((Bsz - h_) & 1) { die_par++; return; }
    int k = (Bsz - h_) / 2;
    if (k > v) { die_v++; return; }
    feas++;
    waysum += binom[v][k];
    hhist[h_]++;
}

static void process(void) {
    omask = 0;
    for (int i = 0; i < R; i++) omask |= 1ULL << O[i];
    /* init at m = 0 (all sides 0) */
    memset(d, 0, sizeof(int) * A);
    h_ = 0; nbad = 0;
    for (int i = 0; i < R; i++)
        for (int j = i + 1; j < R; j++) {
            int x = O[i] + O[j];            /* < 2s, even */
            int c = (x % S) / 2;
            axis_[i][j] = c;
            int sg = (x % N) < S ? 1 : -1;  /* x < 2s so x%N == x */
            contrib[i][j] = sg;
            d[c] += sg;
        }
    for (int i = 0; i < R; i++) {
        int x = (2 * O[i]) % N;
        d[(x % S) / 2] += (x < S) ? 1 : -1;
    }
    {
        int x = (3 * S / 2) % N;
        d[(x % S) / 2] += (x < S) ? 1 : -1;
    }
    h_ = 0; nbad = 0;
    for (int c = 0; c < A; c++) {
        int ad = d[c] < 0 ? -d[c] : d[c];
        h_ += ad;
        if (ad >= 2) nbad++;
    }
    tally();
    /* Gray walk over remaining 2^(R-1)-1 sign classes */
    long total = 1L << (R - 1);
    for (long g = 1; g < total; g++) {
        /* bit that flips between gray(g-1) and gray(g) is ctz(g);
         * sign index i = ctz(g) + 1 (m bit k controls fiber k+1) */
        int bit = __builtin_ctzl(g);
        int i = bit + 1;
        for (int j = 0; j < R; j++) {
            if (j == i) continue;
            int a = j < i ? j : i, b2 = j < i ? i : j;
            int c = axis_[a][b2], s0 = contrib[a][b2];
            contrib[a][b2] = -s0;
            move_term(c, -2 * s0);
        }
        tally();
    }
}

static void rec(int depth, int start) {
    if (depth == R) {
        if ((ocount++ % NW) == WID) process();
        return;
    }
    for (int x = start; x < S / 2; x++) {
        U[depth] = x;
        O[depth] = 2 * x + PAR;
        rec(depth + 1, x + 1);
    }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    if (argc > 4) { NW = atol(argv[3]); WID = atol(argv[4]); }
    N = 2 * S; A = S / 2; Bsz = (S + 1 - R) / 2;
    for (int i = 0; i < 80; i++) {
        binom[i][0] = 1;
        for (int j = 1; j <= i; j++)
            binom[i][j] = binom[i - 1][j - 1] + (j <= i - 1 ? binom[i - 1][j] : 0);
    }
    PAR = 0; ocount = 0; rec(0, 0);
    PAR = 1; ocount = 0; rec(0, 0);
    printf("DIAG s %d r %d b %d NW %ld WID %ld\n", S, R, Bsz, NW, WID);
    printf("DIAG total %lld pure %lld mixed 0\n", c_pure, c_pure);
    printf("DIAG die_odd_mixed 0 die_odd_pure 0 pass_odd_mixed 0\n");
    printf("DIAG die_d2 %lld die_blocked %lld die_hgtb %lld die_par %lld die_v %lld\n",
           die_d2, die_blocked, die_hgtb, die_par, die_v);
    printf("DIAG feas %lld feas_mixed 0 waysum %lld\n", feas, waysum);
    printf("DIAG minD_oddpass %d minD_clean %d\n",
           minD == (1 << 30) ? -1 : minD,
           minD_clean == (1 << 30) ? -1 : minD_clean);
    printf("DIAG hhist");
    for (int i = 0; i < 200; i++) if (hhist[i]) printf(" %d:%lld", i, hhist[i]);
    printf("\n");
    fflush(stdout);
    return 0;
}

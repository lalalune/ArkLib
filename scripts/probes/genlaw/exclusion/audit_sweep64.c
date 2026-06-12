/* AUDITOR-independent generic sweeper for the level-2 balance law.
 * s = 2^j (8/16/32), odd r >= 3, pattern (b, r), b = (s+1-r)/2.
 * Multiset (zeta_n exponents, n = 2s):
 *   products (a_i+a_j) for i<j  U  O_z (2*o_i)  U  B_z (2*b)  U  {3s/2}.
 * Balance: cnt[t] == cnt[t+s] for all t in [0, s).
 * COUNTING METHOD (deliberately different from both prior agents):
 *   per-axis generating polynomial in t (#fibers used):
 *     options on axis c = subsets of ({c, c+A} \ O) with net = -(fixed imbalance)
 *   then DP product, read coefficient [t^b]. No closed-form placement rule.
 * args: s r [nw wid] [rec]   (rec => print feasible class records)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, N, A, R, Bsz, NW = 1, WID = 0, PRINTREC = 0;
static long long total = 0, nclasses = 0, ocount = 0;
static int O[20];

static void process(void) {
    unsigned long long omask = 0;
    for (int i = 0; i < R; i++) omask |= 1ULL << O[i];
    for (long m = 0; m < (1L << (R - 1)); m++) {
        int a[20];
        a[0] = O[0];
        for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
        int cnt[128];
        memset(cnt, 0, sizeof(int) * N);
        for (int i = 0; i < R; i++)
            for (int j = i + 1; j < R; j++)
                cnt[(a[i] + a[j]) % N]++;
        for (int i = 0; i < R; i++) cnt[(2 * O[i]) % N]++;
        cnt[(3 * S / 2) % N]++;
        int ok = 1;
        for (int t = 1; t < S && ok; t += 2)
            if (cnt[t] != cnt[t + S]) ok = 0;
        if (!ok) continue;
        long long dp[80];
        memset(dp, 0, sizeof dp);
        dp[0] = 1;
        int maxt = 0, h = 0, v = 0;
        int forced[48], nf = 0, freeax[48], nv = 0;
        for (int c = 0; c < A && ok; c++) {
            int need = -(cnt[2 * c] - cnt[2 * c + S]);
            int av0 = !(omask & (1ULL << c));
            int av1 = !(omask & (1ULL << (c + A)));
            int p0 = 0, p1 = 0, p2 = 0;
            if (need == 0) {
                p0 = 1;
                if (av0 && av1) { p2 = 1; freeax[nv] = c; }
            } else if (need == 1) {
                if (av0) { p1 = 1; forced[nf] = c; }
            } else if (need == -1) {
                if (av1) { p1 = 1; forced[nf] = c + A; }
            } else { ok = 0; break; }
            if (!p0 && !p1 && !p2) { ok = 0; break; }
            if (need != 0) { h++; nf++; }
            if (p2) { v++; nv++; }
            long long nd[80];
            memset(nd, 0, sizeof nd);
            for (int t = 0; t <= maxt; t++) {
                if (!dp[t]) continue;
                if (p0) nd[t] += dp[t];
                if (p1 && t + 1 <= Bsz) nd[t + 1] += dp[t];
                if (p2 && t + 2 <= Bsz) nd[t + 2] += dp[t];
            }
            memcpy(dp, nd, sizeof dp);
            maxt += (p2 ? 2 : (p1 ? 1 : 0));
            if (maxt > Bsz) maxt = Bsz;
        }
        if (!ok || !dp[Bsz]) continue;
        total += dp[Bsz];
        nclasses++;
        if (PRINTREC) {
            printf("REC");
            for (int i = 0; i < R; i++) printf(" %d", O[i]);
            printf(" | %ld | h %d :", m, h);
            for (int i = 0; i < nf; i++) printf(" %d", forced[i]);
            printf(" | v %d :", v);
            for (int i = 0; i < nv; i++) printf(" %d", freeax[i]);
            printf(" | w %lld\n", dp[Bsz]);
        }
    }
}

static void rec(int depth, int start) {
    if (depth == R) {
        if ((ocount++ % NW) == WID) process();
        return;
    }
    for (int x = start; x < S; x++) { O[depth] = x; rec(depth + 1, x + 1); }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    if (argc > 4) { NW = atoi(argv[3]); WID = atoi(argv[4]); }
    if (argc > 5 && !strcmp(argv[5], "rec")) PRINTREC = 1;
    N = 2 * S; A = S / 2; Bsz = (S + 1 - R) / 2;
    rec(0, 0);
    fprintf(stderr, "AUDIT s=%d r=%d (b=%d) worker %d/%d: classes=%lld waysum=%lld\n",
            S, R, Bsz, WID, NW, nclasses, total);
    printf("TOTAL s=%d r=%d worker %d/%d classes %lld waysum %lld\n",
           S, R, WID, NW, nclasses, total);
    return 0;
}

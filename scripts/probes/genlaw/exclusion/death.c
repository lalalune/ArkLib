/* Instrumented death-census for the level-2 balance law.
 * Based on scripts/probes/genlaw/audit/audit_sweep64.c (same ground-truth
 * feasibility logic, verbatim balance + per-axis accounting), plus:
 *   - cause-of-death classification per (O, signs) config
 *   - empirical test of the parity-purity theorem:
 *       mixed-parity O  <=>  odd-balance failure   (predict exact equivalence)
 *   - histograms: max|d_c| (pure configs), h-b (pure, all |d|<=1)
 *   - flag bitmask census over pure configs
 *   - "pure" mode: enumerate only parity-pure O (valid given purity theorem)
 * usage: ./death s r [pure]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, N, A, R, Bsz, PUREONLY = 0;
static int O[40];

static long long n_configs = 0;
static long long c_mixed = 0, c_mixed_oddpass = 0;   /* predict c_mixed_oddpass == 0 */
static long long c_pure = 0, c_pure_oddfail = 0;     /* predict c_pure_oddfail == 0 */
/* hierarchical cause among pure (odd-balance auto-pass) configs: */
static long long c_d2 = 0, c_block = 0, c_hgb = 0, c_par = 0, c_vcap = 0, c_feas = 0;
static long long feas_ways = 0, feas_classes = 0;
static long long hist_maxd[64];
#define OFF 100
static long long hist_hmb[200];                       /* h - b + OFF, over pure configs with all |d|<=1, no block */
static long long flag_census[32];                     /* bit0 D2, bit1 BLOCK, bit2 HGB, bit3 PAR, bit4 VCAP */

static long long binom(int n, int k) {
    if (k < 0 || k > n) return 0;
    long long r = 1;
    for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
    return r;
}

static void process(void) {
    unsigned long long omask = 0;
    int npar[2] = {0, 0};
    for (int i = 0; i < R; i++) { omask |= 1ULL << O[i]; npar[O[i] & 1]++; }
    int mixed = (npar[0] > 0 && npar[1] > 0);
    for (long m = 0; m < (1L << (R - 1)); m++) {
        n_configs++;
        int a[40];
        a[0] = O[0];
        for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
        int cnt[128];
        memset(cnt, 0, sizeof(int) * N);
        for (int i = 0; i < R; i++)
            for (int j = i + 1; j < R; j++)
                cnt[(a[i] + a[j]) % N]++;
        for (int i = 0; i < R; i++) cnt[(2 * O[i]) % N]++;
        cnt[(3 * S / 2) % N]++;
        int oddok = 1;
        for (int t = 1; t < S && oddok; t += 2)
            if (cnt[t] != cnt[t + S]) oddok = 0;
        if (mixed) { c_mixed++; if (oddok) c_mixed_oddpass++; if (!oddok) continue; }
        else       { c_pure++;  if (!oddok) { c_pure_oddfail++; continue; } }
        /* even-axis accounting (pure configs in practice) */
        int maxd = 0, h = 0, v = 0, nblock = 0;
        for (int c = 0; c < A; c++) {
            int d = cnt[2 * c] - cnt[2 * c + S];
            int ad = d < 0 ? -d : d;
            if (ad > maxd) maxd = ad;
            if (ad == 1) {
                h++;
                /* need a B on the light side: d=+1 -> fiber c+A (adds to cnt[2c+S]);
                   d=-1 -> fiber c (adds to cnt[2c]).  blocked if that fiber is in O. */
                int lf = (d == 1) ? c + A : c;
                if (omask & (1ULL << lf)) nblock++;
            } else if (ad == 0) {
                if (!(omask & (1ULL << c)) && !(omask & (1ULL << (c + A)))) v++;
            }
        }
        hist_maxd[maxd > 63 ? 63 : maxd]++;
        int flags = 0;
        if (maxd >= 2) flags |= 1;
        if (nblock > 0) flags |= 2;
        if (h > Bsz) flags |= 4;
        if (h <= Bsz && ((Bsz - h) & 1)) flags |= 8;
        if (h <= Bsz && !((Bsz - h) & 1) && (Bsz - h) / 2 > v) flags |= 16;
        flag_census[flags]++;
        if (maxd < 2 && nblock == 0) hist_hmb[h - Bsz + OFF]++;
        if (flags & 1) { c_d2++; continue; }
        if (flags & 2) { c_block++; continue; }
        if (flags & 4) { c_hgb++; continue; }
        if (flags & 8) { c_par++; continue; }
        if (flags & 16) { c_vcap++; continue; }
        c_feas++;
        feas_classes++;
        feas_ways += binom(v, (Bsz - h) / 2);
    }
}

static void rec(int depth, int start, int step) {
    if (depth == R) { process(); return; }
    for (int x = start; x < S; x += step) { O[depth] = x; rec(depth + 1, x + step, step); }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    if (argc > 3 && !strcmp(argv[3], "pure")) PUREONLY = 1;
    N = 2 * S; A = S / 2; Bsz = (S + 1 - R) / 2;
    if (PUREONLY) { rec(0, 0, 2); rec(0, 1, 2); }
    else rec(0, 0, 1);
    printf("DEATH s=%d r=%d b=%d pureonly=%d\n", S, R, Bsz, PUREONLY);
    printf("configs %lld | mixed %lld (oddpass %lld) | pure %lld (oddfail %lld)\n",
           n_configs, c_mixed, c_mixed_oddpass, c_pure, c_pure_oddfail);
    printf("pure causes: D2 %lld BLOCK %lld HGB %lld PAR %lld VCAP %lld FEAS %lld\n",
           c_d2, c_block, c_hgb, c_par, c_vcap, c_feas);
    printf("feas classes %lld waysum %lld\n", feas_classes, feas_ways);
    printf("hist max|d| (pure):");
    for (int i = 0; i < 64; i++) if (hist_maxd[i]) printf(" %d:%lld", i, hist_maxd[i]);
    printf("\nhist h-b (pure, |d|<=1, noblock):");
    for (int i = 0; i < 200; i++) if (hist_hmb[i]) printf(" %d:%lld", i - OFF, hist_hmb[i]);
    printf("\nflag census [D2|BLOCK|HGB|PAR|VCAP]:");
    for (int i = 0; i < 32; i++) if (flag_census[i]) printf(" %02d:%lld", i, flag_census[i]);
    printf("\n");
    return 0;
}

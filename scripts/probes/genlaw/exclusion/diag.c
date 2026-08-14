/* diag.c — instrumented per-cause feasibility diagnostic for the level-2 balance law.
 * Derived from scripts/probes/genlaw/audit/audit_sweep64.c (same criterion), but
 * restructured: every (O,m) sign-class is classified by its FIRST failing gate:
 *   G1 odd-self-balance (odd exponents must pair antipodally; B cannot help)
 *   G2 |d_c| >= 2 on some even axis (per-axis B capacity is 1 per side)
 *   G3 forced axis blocked (light-side fiber already in O)
 *   G4 h > b (budget)
 *   G5 (b-h) odd (predicted to NEVER fire: h == b mod 2 is a theorem)
 *   G6 (b-h)/2 > v (free-axis capacity)
 *   else FEASIBLE, ways = C(v,(b-h)/2)
 * Extra instrumentation:
 *   - parity split (p,q) of O: mixed (pq>0) vs pure; counter for mixed configs that
 *     PASS G1 (falsifier for the purity theorem; expected 0)
 *   - D = sum_c |d_c| histogram for all G1-passers (D is h uncapped); min D
 *   - min h among clean (G1-G3 passed) configs  => closest approach to budget b
 *   - h histogram for feasible classes
 * args: s r [NW WID] [rec]
 *   NW/WID: process O-sets with (index % NW)==WID  => NW=K,WID=0 gives a 1/K
 *   deterministic stride sample; full run = NW=1 WID=0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, N, A, R, Bsz;
static long NW = 1, WID = 0;
static int PRINTREC = 0;
static long long ocount = 0;
static int O[32];

static long long c_total = 0, c_pure = 0, c_mixed = 0;
static long long die_odd_mixed = 0, die_odd_pure = 0, pass_odd_mixed = 0;
static long long die_d2 = 0, die_blocked = 0, die_hgtb = 0, die_par = 0, die_v = 0;
static long long feas = 0, waysum = 0, feas_mixed = 0;
static long long dhist[300];   /* D for all G1-passers, capped */
static long long hhist[200];   /* h for feasible */
static int minD_oddpass = 1 << 30;   /* min D among G1-passers (any maxd) */
static int minD_clean = 1 << 30;     /* min h among G1-G3 passers */
static long long nearmiss[8];        /* clean configs with h = b+1 .. b+8 */
static long long recprinted = 0, RECCAP = 300;

static long long binom[80][80];

static void process(void) {
    unsigned long long omask = 0;
    int pq;
    {
        int p = 0;
        for (int i = 0; i < R; i++) { omask |= 1ULL << O[i]; p += (O[i] & 1); }
        pq = p * (R - p);
    }
    for (long m = 0; m < (1L << (R - 1)); m++) {
        int a[32];
        a[0] = O[0];
        for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
        int cnt[300];
        memset(cnt, 0, sizeof(int) * N);
        for (int i = 0; i < R; i++)
            for (int j = i + 1; j < R; j++)
                cnt[(a[i] + a[j]) % N]++;
        for (int i = 0; i < R; i++) cnt[(2 * O[i]) % N]++;
        cnt[(3 * S / 2) % N]++;
        c_total++;
        if (pq) c_mixed++; else c_pure++;
        /* G1: odd self-balance */
        int ok = 1;
        for (int t = 1; t < S && ok; t += 2)
            if (cnt[t] != cnt[t + S]) ok = 0;
        if (!ok) { if (pq) die_odd_mixed++; else die_odd_pure++; continue; }
        if (pq) pass_odd_mixed++;   /* purity falsifier counter */
        /* axes */
        int D = 0, maxd = 0, blocked = 0, v = 0;
        for (int c = 0; c < A; c++) {
            int d = cnt[2 * c] - cnt[2 * c + S];
            int ad = d < 0 ? -d : d;
            D += ad;
            if (ad > maxd) maxd = ad;
            if (ad == 1) {
                int ff = (d == -1) ? c : c + A;  /* light-side fiber, forced */
                if (omask & (1ULL << ff)) blocked++;
            } else if (ad == 0) {
                if (!(omask & (1ULL << c)) && !(omask & (1ULL << (c + A)))) v++;
            }
        }
        dhist[D < 299 ? D : 299]++;
        if (D < minD_oddpass) minD_oddpass = D;
        if (maxd >= 2) { die_d2++; continue; }
        if (blocked)   { die_blocked++; continue; }
        int h = D;
        if (h < minD_clean) minD_clean = h;
        if (h > Bsz) {
            die_hgtb++;
            if (h - Bsz <= 8) nearmiss[h - Bsz - 1]++;
            if (PRINTREC && h - Bsz <= 2 && recprinted < RECCAP) {
                recprinted++;
                printf("NM");
                for (int i = 0; i < R; i++) printf(" %d", O[i]);
                printf(" | m %ld | h %d b %d\n", m, h, Bsz);
            }
            continue;
        }
        if ((Bsz - h) & 1) { die_par++; continue; }
        int k = (Bsz - h) / 2;
        if (k > v) { die_v++; continue; }
        feas++;
        if (pq) feas_mixed++;
        waysum += binom[v][k];
        hhist[h]++;
        if (PRINTREC && recprinted < RECCAP) {
            recprinted++;
            printf("REC");
            for (int i = 0; i < R; i++) printf(" %d", O[i]);
            printf(" | m %ld | h %d v %d w %lld\n", m, h, v, binom[v][k]);
        }
    }
}

static int PUREMODE = 0, PAR = 0;

static void rec(int depth, int start) {
    if (depth == R) {
        if ((ocount++ % NW) == WID) process();
        return;
    }
    if (PUREMODE) {
        /* enumerate O' subset of Z_{S/2}, O = 2*O' + PAR : exactly the
         * parity-pure O-sets (justified by the purity theorem T1) */
        for (int x = start; x < S / 2; x++) {
            O[depth] = 2 * x + PAR;
            rec(depth + 1, x + 1);
        }
    } else {
        for (int x = start; x < S; x++) { O[depth] = x; rec(depth + 1, x + 1); }
    }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    if (argc > 4) { NW = atol(argv[3]); WID = atol(argv[4]); }
    if (argc > 5 && (!strcmp(argv[5], "rec") || !strcmp(argv[5], "purerec"))) PRINTREC = 1;
    if (argc > 5 && (!strcmp(argv[5], "pure") || !strcmp(argv[5], "purerec"))) PUREMODE = 1;
    N = 2 * S; A = S / 2; Bsz = (S + 1 - R) / 2;
    for (int i = 0; i < 80; i++) {
        binom[i][0] = 1;
        for (int j = 1; j <= i; j++)
            binom[i][j] = binom[i - 1][j - 1] + (j <= i - 1 ? binom[i - 1][j] : 0);
    }
    if (PUREMODE) {
        PAR = 0; rec(0, 0);
        PAR = 1; ocount = 0; rec(0, 0);
    } else {
        rec(0, 0);
    }
    printf("DIAG s %d r %d b %d NW %ld WID %ld\n", S, R, Bsz, NW, WID);
    printf("DIAG total %lld pure %lld mixed %lld\n", c_total, c_pure, c_mixed);
    printf("DIAG die_odd_mixed %lld die_odd_pure %lld pass_odd_mixed %lld\n",
           die_odd_mixed, die_odd_pure, pass_odd_mixed);
    printf("DIAG die_d2 %lld die_blocked %lld die_hgtb %lld die_par %lld die_v %lld\n",
           die_d2, die_blocked, die_hgtb, die_par, die_v);
    printf("DIAG feas %lld feas_mixed %lld waysum %lld\n", feas, feas_mixed, waysum);
    printf("DIAG minD_oddpass %d minD_clean %d\n",
           minD_oddpass == (1 << 30) ? -1 : minD_oddpass,
           minD_clean == (1 << 30) ? -1 : minD_clean);
    printf("DIAG nearmiss_h_minus_b_1to8");
    for (int i = 0; i < 8; i++) printf(" %lld", nearmiss[i]);
    printf("\n");
    printf("DIAG dhist");
    for (int i = 0; i < 300; i++) if (dhist[i]) printf(" %d:%lld", i, dhist[i]);
    printf("\n");
    printf("DIAG hhist");
    for (int i = 0; i < 200; i++) if (hhist[i]) printf(" %d:%lld", i, hhist[i]);
    printf("\n");
    fflush(stdout);
    return 0;
}

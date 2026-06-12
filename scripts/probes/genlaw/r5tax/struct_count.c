/* Canonical-frame structural counter for the odd-r marginal strata.
 * Counts ONLY parity-pure configs (purity proven for r=5 at all 2-power s;
 * for other r this is a purity TEST against the audit ground truth).
 * Coordinates: pi in {0,1}; U = {u_1<..<u_r} subset Z_M, M = s/2;
 * sides sm in 2^(r-1) (s_1 = 0 = global-flip quotient).
 * Terms: doubles D_i at axis 2u_i mod M, side [u_i >= M/2];
 *        products P_ij at axis (u_i+u_j) mod M, side [u_i+u_j >= M]^s_i^s_j;
 *        Lambda at axis (M/2 - pi) mod M, side 1.
 * Placement law: per axis d = #side0 - #side1 over terms; feasible iff
 * |d|<=1 all axes, light side of |d|=1 axes not an O-fiber; h = #forced,
 * k = (b-h)/2, v = #(d=0 axes with no O-fiber); ways = C(v,k), b=(s+1-r)/2.
 * usage: ./struct_count s r
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int S, M, R, NP, Bsz;
static int U[16], pairs_i[128], pairs_j[128];
static __int128 ways_pi[2]; static long long cls_pi[2];
static unsigned long long C[80][80];

static void print128(__int128 x) {
    if (x > (__int128)1e18) {
        long long hi = (long long)(x / 1000000000000000000LL);
        long long lo = (long long)(x % 1000000000000000000LL);
        printf("%lld%018lld", hi, lo);
    } else printf("%lld", (long long)x);
}

static int dax[16], rho[16], pax[128], gam[128], pmask[128];
static int olow[64], ohigh[64]; /* O-fiber present at axis side0/side1 */

static void process(int pi) {
    int lam = (M / 2 - pi) % M;
    for (int i = 0; i < R; i++) {
        dax[i] = (2 * U[i]) % M;
        rho[i] = U[i] >= M / 2;
    }
    for (int t = 0; t < NP; t++) {
        int a = U[pairs_i[t]] + U[pairs_j[t]];
        pax[t] = a % M; gam[t] = a >= M;
        pmask[t] = ((pairs_i[t] ? 1 << (pairs_i[t] - 1) : 0) ^
                    (1 << (pairs_j[t] - 1)));
    }
    memset(olow, 0, sizeof(int) * M); memset(ohigh, 0, sizeof(int) * M);
    for (int i = 0; i < R; i++) { if (rho[i]) ohigh[dax[i]] = 1; else olow[dax[i]] = 1; }
    static int d[64], touched[64];
    for (long sm = 0; sm < (1L << (R - 1)); sm++) {
        int nt = 0;
        for (int i = 0; i < R; i++) {
            if (!d[dax[i]] && 1) { }
        }
        /* reset-by-touched scheme */
        memset(d, 0, sizeof(int) * M); /* M<=64: cheap enough */
        int occ_mask_cnt = 0;
        static int seen[64]; memset(seen, 0, sizeof(int) * M);
        for (int i = 0; i < R; i++) {
            d[dax[i]] += rho[i] ? -1 : 1;
            if (!seen[dax[i]]) { seen[dax[i]] = 1; touched[occ_mask_cnt++] = dax[i]; }
        }
        for (int t = 0; t < NP; t++) {
            int sd = gam[t] ^ (__builtin_parity(sm & pmask[t]));
            d[pax[t]] += sd ? -1 : 1;
            if (!seen[pax[t]]) { seen[pax[t]] = 1; touched[occ_mask_cnt++] = pax[t]; }
        }
        d[lam] -= 1;
        if (!seen[lam]) { seen[lam] = 1; touched[occ_mask_cnt++] = lam; }
        int ok = 1, h = 0, v = M - occ_mask_cnt; /* empty axes all free of O */
        for (int x = 0; x < occ_mask_cnt && ok; x++) {
            int c = touched[x], dc = d[c];
            if (dc > 1 || dc < -1) { ok = 0; break; }
            if (dc == 1) { if (ohigh[c]) { ok = 0; break; } h++; }
            else if (dc == -1) { if (olow[c]) { ok = 0; break; } h++; }
            else { if (!olow[c] && !ohigh[c]) v++; }
        }
        if (!ok) continue;
        int kk = Bsz - h;
        if (kk < 0 || (kk & 1)) continue;
        kk >>= 1;
        if (kk > v) continue;
        ways_pi[pi] += (__int128)C[v][kk];
        cls_pi[pi]++;
    }
}

static void rec(int depth, int start, int pi) {
    if (depth == R) { process(pi); return; }
    for (int x = start; x < M; x++) { U[depth] = x; rec(depth + 1, x + 1, pi); }
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    M = S / 2; Bsz = (S + 1 - R) / 2; NP = 0;
    for (int i = 0; i < R; i++) for (int j = i + 1; j < R; j++)
        { pairs_i[NP] = i; pairs_j[NP] = j; NP++; }
    for (int i = 0; i < 80; i++) { C[i][0] = 1;
        for (int j = 1; j <= i; j++) C[i][j] = C[i-1][j-1] + (j <= i-1 ? C[i-1][j] : 0); }
    for (int pi = 0; pi < 2; pi++) rec(0, 0, pi);
    printf("STRUCT s=%d r=%d (b=%d): classes pi0 %lld pi1 %lld total %lld | ways pi0 ",
           S, R, Bsz, cls_pi[0], cls_pi[1], cls_pi[0] + cls_pi[1]);
    print128(ways_pi[0]); printf(" pi1 "); print128(ways_pi[1]);
    printf(" total "); print128(ways_pi[0] + ways_pi[1]); printf("\n");
    return 0;
}

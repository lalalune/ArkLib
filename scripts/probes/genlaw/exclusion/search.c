/* search.c — randomized witness search for feasible (O,m) sign-classes at large s.
 * Samples parity-pure configs (justified: purity theorem T1 says all feasible
 * configs are pure), applies the exact per-config criterion (same gates as
 * diag.c), and for each feasible class constructs an explicit B-completion:
 *   B = forced light-side fibers  U  first k free axes as antipodal fiber pairs
 * printing a full witness line for independent re-verification:
 *   HIT s <s> r <r> | O <o1..or> | m <m> | B <f1..fb>
 * args: s r ntrials seed [maxhits]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static uint64_t rng_state;
static uint64_t rnd(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    int S = atoi(argv[1]), R = atoi(argv[2]);
    long long NT = atoll(argv[3]);
    rng_state = strtoull(argv[4], 0, 10);
    long long maxhits = argc > 5 ? atoll(argv[5]) : 25;
    int N = 2 * S, A = S / 2, Bsz = (S + 1 - R) / 2, M = S / 2;
    long long hits = 0, printed = 0, clean = 0;
    int minDclean = 1 << 30, minDany = 1 << 30;
    static int cnt[1100];
    int O[32], a[32], inO[1100], op[32];
    for (long long t = 0; t < NT; t++) {
        int par = rnd() & 1;
        /* random distinct R-subset of Z_M */
        int k = 0;
        memset(inO, 0, sizeof(int) * M);
        while (k < R) {
            int x = rnd() % M;
            if (!inO[x]) { inO[x] = 1; op[k++] = x; }
        }
        for (int i = 0; i < R; i++) O[i] = 2 * op[i] + par;
        long m = (long)(rnd() & ((1L << (R - 1)) - 1));
        a[0] = O[0];
        for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
        memset(cnt, 0, sizeof(int) * N);
        for (int i = 0; i < R; i++)
            for (int j = i + 1; j < R; j++)
                cnt[(a[i] + a[j]) % N]++;
        for (int i = 0; i < R; i++) cnt[(2 * O[i]) % N]++;
        cnt[(3 * S / 2) % N]++;
        /* pure => no odd exponents; gates G2..G6 */
        memset(inO, 0, sizeof(int) * S);
        for (int i = 0; i < R; i++) inO[O[i]] = 1;
        int D = 0, maxd = 0, blocked = 0, v = 0, nf = 0, nva = 0;
        int forced[600], freeax[600];
        for (int c = 0; c < A; c++) {
            int d = cnt[2 * c] - cnt[2 * c + S];
            int ad = d < 0 ? -d : d;
            D += ad;
            if (ad > maxd) maxd = ad;
            if (ad == 1) {
                int ff = (d == -1) ? c : c + A;
                if (inO[ff]) blocked++; else forced[nf++] = ff;
            } else if (ad == 0) {
                if (!inO[c] && !inO[c + A]) { freeax[nva++] = c; v++; }
            }
        }
        if (D < minDany) minDany = D;
        if (maxd >= 2 || blocked) continue;
        clean++;
        if (D < minDclean) minDclean = D;
        int h = D;
        if (h > Bsz) continue;
        if ((Bsz - h) & 1) { printf("PARITY_VIOLATION\n"); continue; }
        int kk = (Bsz - h) / 2;
        if (kk > v) continue;
        hits++;
        if (printed < maxhits) {
            printed++;
            printf("HIT s %d r %d | O", S, R);
            for (int i = 0; i < R; i++) printf(" %d", O[i]);
            printf(" | m %ld | B", m);
            for (int i = 0; i < nf; i++) printf(" %d", forced[i]);
            for (int i = 0; i < kk; i++) printf(" %d %d", freeax[i], freeax[i] + A);
            printf("\n");
        }
    }
    printf("SEARCH s %d r %d b %d trials %lld clean %lld hits %lld minDclean %d minDany %d\n",
           S, R, Bsz, NT, clean, hits, minDclean == (1 << 30) ? -1 : minDclean,
           minDany == (1 << 30) ? -1 : minDany);
    return 0;
}

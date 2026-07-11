/* INDEPENDENT AUDIT KERNEL — written from scratch by the adversarial auditor.
 * Differences from census_kernel.c on purpose:
 *   - functional AND order-16 Newton divided difference computed separately, cross-asserted;
 *   - interpolation via Newton form over ALL 17 subset points (not Lagrange over first 16);
 *   - direct counters for agree==17 vs agree>=18, and agree==17 codewords are EMITTED
 *     (the production kernel only derived the 17-layer arithmetically);
 *   - hard error exits on any internal inconsistency.
 * usage: ./audit_kernel <lam> <i0> <out_agree18> <out_agree17>
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#define P 3221225473ULL
#define N 32
#define TS 17 /* k+1 */

static uint64_t mulm(uint64_t a, uint64_t b) { return a * b % P; }
static uint64_t powm(uint64_t b, uint64_t e) {
    uint64_t r = 1; b %= P;
    while (e) { if (e & 1) r = mulm(r, b); b = mulm(b, b); e >>= 1; }
    return r;
}
static uint64_t invm(uint64_t a) { return powm(a, P - 2); }

static uint64_t X[N], WD[N], ID[N][N];

int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: %s lam i0 out18 out17\n", argv[0]); return 2; }
    uint64_t lam = strtoull(argv[1], 0, 10) % P;
    int i0 = atoi(argv[2]);
    FILE *o18 = fopen(argv[3], "w"), *o17 = fopen(argv[4], "w");
    if (!o18 || !o17) { perror("fopen"); return 2; }

    uint64_t h = powm(5, (P - 1) / N);
    for (int i = 0; i < N; i++) X[i] = powm(h, (uint64_t)i);
    for (int i = 0; i < N; i++)
        WD[i] = (powm(X[i], 18) + mulm(lam, powm(X[i], 16))) % P;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            if (i != j) ID[i][j] = invm((X[i] + P - X[j]) % P);

    int c[TS];
    for (int t = 0; t < TS; t++) c[t] = i0 + t;
    if (c[TS - 1] >= N) {
        fprintf(stderr, "AUD chunk %d: subsets=0 pass=0 a17=0 a18=0\n", i0);
        return 0;
    }
    uint64_t nsub = 0, npass = 0, n17 = 0, n18 = 0;
    for (;;) {
        nsub++;
        uint64_t s = 0; /* finite-difference functional over the 17 points */
        for (int t = 0; t < TS; t++) {
            uint64_t term = WD[c[t]];
            const uint64_t *row = ID[c[t]];
            for (int u = 0; u < TS; u++)
                if (u != t) term = mulm(term, row[c[u]]);
            s += term;
        }
        if (s % P == 0) {
            npass++;
            /* Newton divided-difference table over all 17 points */
            uint64_t dd[TS];
            for (int t = 0; t < TS; t++) dd[t] = WD[c[t]];
            for (int j = 1; j < TS; j++)
                for (int t = TS - 1; t >= j; t--)
                    dd[t] = mulm((dd[t] + P - dd[t - 1]) % P, ID[c[t]][c[t - j]]);
            if (dd[TS - 1] != 0) {
                fprintf(stderr, "FATAL: functional=0 but top divided difference != 0 (chunk %d)\n", i0);
                return 9;
            }
            uint64_t ev[N]; int agree = 0;
            for (int i = 0; i < N; i++) {
                uint64_t acc = dd[TS - 1];
                for (int t = TS - 2; t >= 0; t--)
                    acc = (mulm(acc, (X[i] + P - X[c[t]]) % P) + dd[t]) % P;
                ev[i] = acc;
                agree += (acc == WD[i]);
            }
            if (agree >= 18) {
                n18++;
                for (int i = 0; i < N; i++)
                    fprintf(o18, "%llu%c", (unsigned long long)ev[i], i == N - 1 ? '\n' : ' ');
            } else if (agree == 17) {
                n17++;
                for (int i = 0; i < N; i++)
                    fprintf(o17, "%llu%c", (unsigned long long)ev[i], i == N - 1 ? '\n' : ' ');
            } else {
                fprintf(stderr, "FATAL: pass with agree=%d < 17 (chunk %d)\n", agree, i0);
                return 8;
            }
        }
        int t = TS - 1;
        while (t >= 1 && c[t] == N - TS + t) t--;
        if (t < 1) break;
        c[t]++;
        for (int u = t + 1; u < TS; u++) c[u] = c[u - 1] + 1;
    }
    fclose(o18); fclose(o17);
    fprintf(stderr, "AUD chunk %d: subsets=%llu pass=%llu a17=%llu a18=%llu\n",
            i0, (unsigned long long)nsub, (unsigned long long)npass,
            (unsigned long long)n17, (unsigned long long)n18);
    return 0;
}

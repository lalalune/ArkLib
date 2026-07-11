/* lineword_n32.c — EXACT codeword-list of the line word w_i = x_i^EHI + LAM*x_i^ELO on mu_32,
 * over a NON-FERMAT prime q ~ 2^20 (q==1 mod 32). Generalizes census_kernel.c to our prize-regime
 * thin field. Counts the DISTINCT deg<K codeword list at agreement >= A by enumerating K-subsets
 * of the agreement structure (interpolate, check agree>=A, dedup by 64-bit hash of evals).
 *
 * Build: gcc -O3 -march=native -DQ=1048609 -DGEN=<g> -DEHI=.. -DELO=.. -DLAM=.. -DAA=.. \
 *        -DKK=.. lineword_n32.c -o lw
 * Usage: ./lw <i0> <outfile>   (chunk by smallest index i0; emit one line per passing codeword:
 *        the A>=-agreement and a 64-bit signature hash; post-pass dedups across chunks.)
 *
 * To keep memory bounded we DO NOT store all codewords; we emit (agreement, sig) and dedup in
 * Python. For tractable lists (<<1e7) this is fine. We also print the per-chunk raw pass count.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#ifndef Q
#define Q 1048609ULL
#endif
#ifndef NN
#define NN 32
#endif
#ifndef KK
#define KK 16
#endif
#ifndef AA
#define AA 20
#endif
#ifndef EHI
#define EHI 17
#endif
#ifndef ELO
#define ELO 16
#endif
#ifndef LAM
#define LAM 1ULL
#endif
#ifndef GEN
#define GEN 0ULL   /* if 0, find order-NN generator at runtime */
#endif

static uint64_t H[NN], W[NN], INVD[NN][NN];

static uint64_t pw(uint64_t b, uint64_t e) {
    uint64_t r = 1; b %= Q;
    while (e) { if (e & 1) r = r * b % Q; b = b * b % Q; e >>= 1; }
    return r;
}
static uint64_t inv(uint64_t a) { return pw(a, Q - 2); }

static uint64_t find_gen(void) {
    for (uint64_t g = 2; g < Q; g++) {
        if (pw(g, NN) != 1) continue;
        int ok = 1;
        for (int d = 1; d < NN; d++) if (NN % d == 0 && d < NN && pw(g, d) == 1) { ok = 0; break; }
        if (ok) return g;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: %s <i0> <outfile>\n", argv[0]); return 2; }
    int i0 = atoi(argv[1]);
    FILE *out = fopen(argv[2], "w");
    if (!out) { perror("fopen"); return 2; }

    uint64_t g = GEN ? GEN : find_gen();
    if (!g) { fprintf(stderr, "no order-%d generator in F_%llu\n", NN, (unsigned long long)Q); return 2; }
    for (int i = 0; i < NN; i++) H[i] = pw(g, i);
    for (int i = 0; i < NN; i++) W[i] = (pw(H[i], EHI) + LAM % Q * pw(H[i], ELO)) % Q;
    for (int i = 0; i < NN; i++)
        for (int j = 0; j < NN; j++)
            if (i != j) INVD[i][j] = inv((H[i] + Q - H[j]) % Q);

    /* Enumerate (K+1)-subsets with smallest element i0 (proven census design). The functional
     * s = sum_t W[c_t] * prod_{u!=t} INVD[c_t][c_u] vanishes iff the K+1 points (H[c],W[c]) lie
     * on a common deg<K polynomial. On a pass, interpolate from the first K points, evaluate at
     * all NN points, count agreement with W; emit (agree, sig) if agree>=AA. Every codeword in
     * the list at agreement >=AA (>=K+1) is found by some (K+1)-subset of its agreement set;
     * Python dedups by sig. */
    const int TSZ = KK + 1;
    int c[KK + 1];
    c[0] = i0;
    for (int t = 1; t < TSZ; t++) c[t] = i0 + t;
    if (c[TSZ - 1] >= NN) { fclose(out); return 0; }

    uint64_t n_sub = 0, n_pass = 0, n_emit = 0;
    for (;;) {
        n_sub++;
        uint64_t s = 0;
        for (int t = 0; t < TSZ; t++) {
            const uint64_t *row = INVD[c[t]];
            uint64_t lam = W[c[t]];
            for (int u = 0; u < TSZ; u++)
                if (u != t) lam = lam * row[c[u]] % Q;
            s += lam;
        }
        if (s % Q == 0) {
            n_pass++;
            uint64_t ev[NN];
            for (int jx = 0; jx < NN; jx++) {
                uint64_t tot = 0;
                for (int t = 0; t < KK; t++) {
                    uint64_t num = 1, den = 1;
                    for (int u = 0; u < KK; u++) {
                        if (u == t) continue;
                        num = num * ((H[jx] + Q - H[c[u]]) % Q) % Q;
                        den = den * ((H[c[t]] + Q - H[c[u]]) % Q) % Q;
                    }
                    tot = (tot + W[c[t]] * num % Q * inv(den)) % Q;
                }
                ev[jx] = tot;
            }
            int agree = 0;
            for (int i = 0; i < NN; i++) agree += (ev[i] == W[i]);
            if (agree >= AA) {
                uint64_t sig = 1469598103934665603ULL;
                for (int i = 0; i < NN; i++) { sig ^= ev[i]; sig *= 1099511628211ULL; }
                fprintf(out, "%d %llu\n", agree, (unsigned long long)sig);
                n_emit++;
            }
        }
        int t = TSZ - 1;
        while (t >= 1 && c[t] == NN - TSZ + t) t--;
        if (t < 1) break;
        c[t]++;
        for (int u = t + 1; u < TSZ; u++) c[u] = c[u - 1] + 1;
    }
    fclose(out);
    fprintf(stderr, "chunk i0=%d: subsets=%llu pass=%llu emit(agree>=%d)=%llu\n",
            i0, (unsigned long long)n_sub, (unsigned long long)n_pass, AA,
            (unsigned long long)n_emit);
    return 0;
}

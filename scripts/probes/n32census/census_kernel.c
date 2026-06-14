/* census_kernel.c — finite-difference functional sweep for the exact beyond-Johnson list.
 * Build (n=32 production): gcc -O3 -march=native -o census32 census_kernel.c
 * Build (n=16 calibration): gcc -O3 -march=native -DCAL16 -o census16 census_kernel.c
 * Usage: ./census32 <i0> <outfile>   — sweeps all (K+1)-subsets of {0..N-1} with min element i0.
 * Emits one line per PASSING subset whose interpolant agrees >= A: the N evaluations,
 * space-separated. Dedup + verification + classification is the Python post-pass's job.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define P 2013265921ULL  /* BabyBear 15*2^27+1; compile-time constant => gcc strength-reduces % */
#define G0 31ULL         /* smallest primitive root (range(2,200) convention) */

#ifdef CAL16
#define N 16
#define K 8
#ifndef A
#define A 9
#endif
#define E_HI 10
#define E_LO 8
#else
#define N 32
#define K 16
#ifndef A
#define A 18
#endif
#define E_HI 18
#define E_LO 16
#endif
#define T_SZ (K + 1)
#ifndef LAM
#define LAM 284861408ULL /* -g0^((p-1)/4) mod p : the probe-max() fiber-3/fiber-35 lambda */
#endif

static uint64_t H[N], W[N], INVD[N][N];

static uint64_t pw(uint64_t b, uint64_t e) {
    uint64_t r = 1; b %= P;
    while (e) { if (e & 1) r = r * b % P; b = b * b % P; e >>= 1; }
    return r;
}
static uint64_t inv(uint64_t a) { return pw(a, P - 2); }

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: %s <i0> <outfile>\n", argv[0]); return 2; }
    int i0 = atoi(argv[1]);
    FILE *out = fopen(argv[2], "w");
    if (!out) { perror("fopen"); return 2; }

    uint64_t h = pw(G0, (P - 1) / N);
    for (int i = 0; i < N; i++) H[i] = pw(h, i);
    for (int i = 0; i < N; i++) W[i] = (pw(H[i], E_HI) + LAM * pw(H[i], E_LO)) % P;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            if (i != j) INVD[i][j] = inv((H[i] + P - H[j]) % P);

    int c[T_SZ];
    c[0] = i0;
    for (int t = 1; t < T_SZ; t++) c[t] = i0 + t;
    if (c[T_SZ - 1] >= N) { fclose(out); return 0; }

    uint64_t n_subsets = 0, n_pass = 0, n_agree = 0;
    for (;;) {
        n_subsets++;
        /* functional: s = sum_t W[c_t] * prod_{u != t} INVD[c_t][c_u] */
        uint64_t s = 0;
        for (int t = 0; t < T_SZ; t++) {
            const uint64_t *row = INVD[c[t]];
            uint64_t lam = W[c[t]];
            for (int u = 0; u < T_SZ; u++)
                if (u != t) lam = lam * row[c[u]] % P;
            s += lam;
        }
        if (s % P == 0) {
            n_pass++;
            /* interpolate deg<K poly from c[0..K-1], evaluate at all N points */
            uint64_t ev[N];
            for (int jx = 0; jx < N; jx++) {
                uint64_t tot = 0;
                for (int t = 0; t < K; t++) {
                    uint64_t num = 1, den = 1;
                    for (int u = 0; u < K; u++) {
                        if (u == t) continue;
                        num = num * ((H[jx] + P - H[c[u]]) % P) % P;
                        den = den * ((H[c[t]] + P - H[c[u]]) % P) % P;
                    }
                    tot = (tot + W[c[t]] * num % P * inv(den)) % P;
                }
                ev[jx] = tot;
            }
            int agree = 0;
            for (int i = 0; i < N; i++) agree += (ev[i] == W[i]);
            if (agree >= A) {
                n_agree++;
                for (int i = 0; i < N; i++)
                    fprintf(out, "%llu%c", (unsigned long long)ev[i], i + 1 == N ? '\n' : ' ');
                if (n_agree > 20000000ULL) {  /* abort guard: enormous-list blowout */
                    fprintf(stderr, "ABORT chunk i0=%d: >2e7 passing emissions\n", i0);
                    fclose(out); return 3;
                }
            }
        }
        /* next K-combination of {i0+1..N-1} in lex order (c[0] fixed) */
        int t = T_SZ - 1;
        while (t >= 1 && c[t] == N - T_SZ + t) t--;
        if (t < 1) break;
        c[t]++;
        for (int u = t + 1; u < T_SZ; u++) c[u] = c[u - 1] + 1;
    }
    fclose(out);
    fprintf(stderr, "chunk i0=%d: subsets=%llu functional-pass=%llu agree>=%d-emissions=%llu\n",
            i0, (unsigned long long)n_subsets, (unsigned long long)n_pass, A,
            (unsigned long long)n_agree);
    return 0;
}

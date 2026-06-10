/* qline_kernel.c — LINE version of the C(N,K+1)-subset finite-difference sweep
 * for the deep quotient line  u0 + gamma*u1,  u0 = x^RM/(x^2-w),  u1 = 1/(x^2-w)
 * on H = mu_N over BabyBear (issue #232 level-2 family, second data point n=32).
 *
 * Build n=32:  gcc -O3 -march=native -funroll-loops -o qline32 qline_kernel.c
 * Build n=16:  gcc -O3 -march=native -funroll-loops -DCAL16 -o qline16 qline_kernel.c
 * Usage: ./qline32 <i0> <records.txt> <floor.bin>
 *   sweeps all (K+1)-subsets of {0..N-1} whose minimum element is i0.
 *
 * Conventions:
 *   n=32 (O87): H[i] = (31^((P-1)/32))^i ; z = smallest >=5 with z^32 != 1 -> w = z^2.
 *   n=16 (CAL16, probe_qline_census.py bit-for-bit): generator search base 3
 *     (x=3,4,..., g = x^((P-1)/16), need g != 1 and g^8 != 1), same z search.
 *
 * Per subset T: lam_t = prod_{u != t} (x_t - x_u)^{-1};
 *   SA = sum_t lam_t*u0(x_t); SB = sum_t lam_t*u1(x_t)   (functional = SA + gamma*SB).
 *   SB==0 && SA!=0 : no gamma satisfies T -> counter sb0_only (cannot sit inside any
 *                    agreement set: a codeword's functional on T would force SA=-gamma*SB=0).
 *   SB==0 && SA==0 : EVERY gamma satisfies T (degenerate every-gamma layer)
 *                    -> counter deg_both + "DEG" record line (first 1000 enumerated).
 *   else gamma = -SA/SB.  The deg<K interpolant of y = (u0+gamma*u1)|T agrees with y on
 *   all K+1 points of T by construction (functional zero <=> 17-pt consistency), so
 *   agree >= K+1 ALWAYS; count extra agreements on the N-(K+1) off-nodes via the
 *   division-free barycentric residual  num_j == y_j * den_j  with 17-node weights lam.
 *     extra == 0 (agree == K+1 exactly): append uint32 gamma to floor.bin
 *                                        (CAL16: ALSO emit the full record).
 *     extra  > 0 (agree >= K+2)        : full record "gamma agree ev[0..N-1]".
 * Abort guard: > 10^7 full-record emissions in one chunk -> exit 3.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define P 2013265921ULL

#ifdef CAL16
#define N 16
#define K 8
#define RM 10          /* r*m = 5*2 */
#else
#define N 32
#define K 16
#define RM 18          /* r*m = 9*2 */
#endif
#define T_SZ (K + 1)

static uint64_t H[N], U0[N], U1[N], INVD[N][N];

static uint64_t pw(uint64_t b, uint64_t e) {
    uint64_t r = 1; b %= P;
    while (e) { if (e & 1) r = r * b % P; b = b * b % P; e >>= 1; }
    return r;
}
static uint64_t inv(uint64_t a) { return pw(a, P - 2); }

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s <i0> <records.txt> <floor.bin>\n", argv[0]); return 2; }
    int i0 = atoi(argv[1]);
    FILE *rec = fopen(argv[2], "w");
    FILE *bin = fopen(argv[3], "wb");
    if (!rec || !bin) { perror("fopen"); return 2; }

    /* --- domain --- */
#ifdef CAL16
    uint64_t g = 0;
    for (uint64_t x = 3;; x++) {
        uint64_t cnd = pw(x, (P - 1) / N);
        if (cnd != 1 && pw(cnd, N / 2) != 1) { g = cnd; break; }
    }
#else
    uint64_t g = pw(31, (P - 1) / N);
#endif
    if (pw(g, N) != 1 || pw(g, N / 2) == 1) { fprintf(stderr, "bad generator\n"); return 2; }
    for (int i = 0; i < N; i++) H[i] = pw(g, i);
    uint64_t z = 5;
    while (pw(z, N) == 1) z++;
    uint64_t w = z * z % P;
    for (int i = 0; i < N; i++) {
        uint64_t d = (H[i] * H[i] % P + P - w) % P;
        if (d == 0) { fprintf(stderr, "x^2 = w on H!?\n"); return 2; }
        U1[i] = inv(d);
        U0[i] = pw(H[i], RM) * U1[i] % P;
    }
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            if (i != j) INVD[i][j] = inv((H[i] + P - H[j]) % P);
    if (i0 == 0) fprintf(stderr, "domain: g=%llu z=%llu w=%llu\n",
                         (unsigned long long)g, (unsigned long long)z, (unsigned long long)w);

    int c[T_SZ];
    c[0] = i0;
    for (int t = 1; t < T_SZ; t++) c[t] = i0 + t;
    if (c[T_SZ - 1] >= N) {
        fprintf(stderr, "chunk i0=%d: subsets=0 sb0_only=0 deg_both=0 floor=0 recs=0\n", i0);
        fclose(rec); fclose(bin); return 0;
    }

    uint64_t n_sub = 0, n_sb0 = 0, n_deg = 0, n_floor = 0, n_rec = 0;
    uint64_t lam[T_SZ], A[T_SZ], B[T_SZ], Zt[T_SZ];
    uint8_t inT[N];
    memset(inT, 0, sizeof inT);

    for (;;) {
        n_sub++;
        uint64_t SA = 0, SB = 0;
        for (int t = 0; t < T_SZ; t++) {
            const uint64_t *row = INVD[c[t]];
            uint64_t l = row[c[0 == t ? 1 : 0]];
            for (int u = (0 == t ? 2 : 1); u < T_SZ; u++)
                if (u != t) l = l * row[c[u]] % P;
            lam[t] = l;
            A[t] = l * U0[c[t]] % P;
            B[t] = l * U1[c[t]] % P;
            SA += A[t]; SB += B[t];
        }
        SA %= P; SB %= P;
        if (SB == 0) {
            if (SA == 0) {
                n_deg++;
                if (n_deg <= 1000) {
                    fprintf(rec, "DEG");
                    for (int t = 0; t < T_SZ; t++) fprintf(rec, " %d", c[t]);
                    fprintf(rec, "\n");
                }
            } else n_sb0++;
        } else {
            uint64_t gamma = (P - SA) % P * inv(SB) % P;
            for (int t = 0; t < T_SZ; t++) Zt[t] = (A[t] + gamma * B[t]) % P;
            for (int t = 0; t < T_SZ; t++) inT[c[t]] = 1;
            int extra = 0;
            for (int j = 0; j < N; j++) {
                if (inT[j]) continue;
                uint64_t num = 0, den = 0;
                const uint64_t *colj = INVD[j];
                for (int t = 0; t < T_SZ; t++) {
                    uint64_t e = colj[c[t]];
                    num += Zt[t] * e % P;
                    den += lam[t] * e % P;
                }
                num %= P; den %= P;
                uint64_t yj = (U0[j] + gamma * U1[j]) % P;
                if (num == yj * den % P) extra++;
            }
            if (extra == 0) {
                n_floor++;
                uint32_t g32 = (uint32_t)gamma;
                fwrite(&g32, 4, 1, bin);
            }
#ifdef CAL16
            if (1) {   /* CAL16: full record for every non-degenerate subset */
#else
            if (extra > 0) {
#endif
                /* full evaluation: on-node ev = y; off-node ev = num/den (barycentric) */
                uint64_t ev[N];
                int agree = 0;
                for (int j = 0; j < N; j++) {
                    if (inT[j]) { ev[j] = (U0[j] + gamma * U1[j]) % P; agree++; continue; }
                    uint64_t num = 0, den = 0;
                    const uint64_t *colj = INVD[j];
                    for (int t = 0; t < T_SZ; t++) {
                        uint64_t e = colj[c[t]];
                        num += Zt[t] * e % P;
                        den += lam[t] * e % P;
                    }
                    num %= P; den %= P;
                    ev[j] = num * inv(den) % P;
                    uint64_t yj = (U0[j] + gamma * U1[j]) % P;
                    if (ev[j] == yj) agree++;
                }
                if (agree != T_SZ + extra) { fprintf(stderr, "INTERNAL agree mismatch\n"); return 4; }
                n_rec++;
                fprintf(rec, "%llu %d", (unsigned long long)gamma, agree);
                for (int j = 0; j < N; j++) fprintf(rec, " %llu", (unsigned long long)ev[j]);
                fprintf(rec, "\n");
                if (n_rec > 10000000ULL) {
                    fprintf(stderr, "ABORT chunk i0=%d: >1e7 record emissions\n", i0);
                    fclose(rec); fclose(bin); return 3;
                }
            }
            for (int t = 0; t < T_SZ; t++) inT[c[t]] = 0;
        }
        /* next (T_SZ-1)-combination of {i0+1..N-1} in lex order (c[0] fixed) */
        int t = T_SZ - 1;
        while (t >= 1 && c[t] == N - T_SZ + t) t--;
        if (t < 1) break;
        c[t]++;
        for (int u = t + 1; u < T_SZ; u++) c[u] = c[u - 1] + 1;
    }
    fclose(rec); fclose(bin);
    fprintf(stderr, "chunk i0=%d: subsets=%llu sb0_only=%llu deg_both=%llu floor=%llu recs=%llu\n",
            i0, (unsigned long long)n_sub, (unsigned long long)n_sb0,
            (unsigned long long)n_deg, (unsigned long long)n_floor, (unsigned long long)n_rec);
    return 0;
}

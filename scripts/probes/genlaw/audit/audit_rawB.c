/* AUDITOR raw per-class brute force: ZERO structural assumptions.
 * For one (O, mask) at given (s, r): enumerate ALL C(s-r, b) B-subsets of
 * Z_s \ O, build the full multiset, check antipodal balance directly.
 * args: s r o1 ... or mask
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int S = atoi(argv[1]), R = atoi(argv[2]);
    int N = 2 * S, B = (S + 1 - R) / 2;
    int O[20];
    for (int i = 0; i < R; i++) O[i] = atoi(argv[3 + i]);
    long m = atol(argv[3 + R]);
    int a[20];
    a[0] = O[0];
    for (int i = 1; i < R; i++) a[i] = O[i] + S * ((m >> (i - 1)) & 1);
    int base[256], nb = 0;
    for (int i = 0; i < R; i++)
        for (int j = i + 1; j < R; j++) base[nb++] = (a[i] + a[j]) % N;
    for (int i = 0; i < R; i++) base[nb++] = (2 * O[i]) % N;
    base[nb++] = (3 * S / 2) % N;
    int rest[64], nr = 0;
    for (int z = 0; z < S; z++) {
        int ino = 0;
        for (int i = 0; i < R; i++) if (O[i] == z) ino = 1;
        if (!ino) rest[nr++] = z;
    }
    int fixed[128];
    memset(fixed, 0, sizeof(int) * N);
    for (int t = 0; t < nb; t++) fixed[base[t]]++;
    int idx[40];
    for (int i = 0; i < B; i++) idx[i] = i;
    long long sols = 0, tot = 0;
    while (1) {
        tot++;
        int cnt[128];
        memcpy(cnt, fixed, sizeof(int) * N);
        for (int i = 0; i < B; i++) cnt[(2 * rest[idx[i]]) % N]++;
        int ok = 1;
        for (int t = 0; t < S; t++)
            if (cnt[t] != cnt[t + S]) { ok = 0; break; }
        sols += ok;
        int i = B - 1;
        while (i >= 0 && idx[i] == nr - B + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < B; j++) idx[j] = idx[j - 1] + 1;
    }
    printf("RAWB s=%d r=%d O=(", S, R);
    for (int i = 0; i < R; i++) printf("%d%s", O[i], i + 1 < R ? "," : "");
    printf(") mask=%ld : solutions = %lld (of %lld subsets)\n", m, sols, tot);
    return 0;
}

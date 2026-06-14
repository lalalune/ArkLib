/* RAW exhaustive B-enumeration for one (O,sigma) class at n=64 (s=32).
 * Zero structural assumptions: for every 15-subset B of Z_32 \ O, build the
 * full 22-term multiset {x1x2,x1x3,x2x3} u B_z u O_z u {-z*} as zeta_64
 * exponents and check antipodal balance n[m]==n[m+32] for all m in 0..31.
 * argv: o1 o2 o3 s12 s13  -> prints solution count.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int O[3] = {atoi(argv[1]), atoi(argv[2]), atoi(argv[3])};
    int s12 = atoi(argv[4]), s13 = atoi(argv[5]);
    int d[3] = {0, s12, s13};
    int a[3];
    for (int i = 0; i < 3; i++) a[i] = O[i] + 32 * d[i];
    int base[7] = {(a[0]+a[1]) % 64, (a[0]+a[2]) % 64, (a[1]+a[2]) % 64,
                   (2*O[0]) % 64, (2*O[1]) % 64, (2*O[2]) % 64, 48};
    int rest[32], nr = 0;
    for (int z = 0; z < 32; z++)
        if (z != O[0] && z != O[1] && z != O[2]) rest[nr++] = z;
    /* nr = 29; enumerate 15-combinations via odometer */
    int idx[15];
    for (int i = 0; i < 15; i++) idx[i] = i;
    long long cnt_sol = 0, total = 0;
    while (1) {
        total++;
        int n[64];
        memset(n, 0, sizeof n);
        for (int t = 0; t < 7; t++) n[base[t]]++;
        for (int i = 0; i < 15; i++) n[(2 * rest[idx[i]]) % 64]++;
        int ok = 1;
        for (int m = 0; m < 32; m++)
            if (n[m] != n[m + 32]) { ok = 0; break; }
        cnt_sol += ok;
        /* next combination */
        int i = 14;
        while (i >= 0 && idx[i] == nr - 15 + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < 15; j++) idx[j] = idx[j - 1] + 1;
    }
    printf("O=(%d,%d,%d) sig=(%d,%d) : raw solutions = %lld  (of %lld subsets)\n",
           O[0], O[1], O[2], s12, s13, cnt_sol, total);
    return 0;
}

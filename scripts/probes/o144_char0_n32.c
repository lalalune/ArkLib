// O144: char-0 layer at (32,8) depth-1: count 10-subsets A of mu_32 with e2(A)=0 in Z[zeta_32].
// Representation: Z[x]/(x^16+1). 2*e2 = s1^2 - s2 where s1 = sum zeta^j, s2 = sum zeta^(2j).
#include <stdio.h>
#include <stdint.h>
#include <string.h>
static inline void zadd(int64_t *v, int j){ j &= 31; if (j < 16) v[j]++; else v[j-16]--; }
int main(void){
    // enumerate 10-subsets of {0..31} via Gosper
    uint64_t set = (1ULL<<10) - 1, limit = 1ULL<<32;
    long long count = 0, checked = 0;
    int idx[10];
    int64_t s1[16], s2[16], sq[31];
    long long examples = 0;
    while (set < limit){
        int n = 0;
        uint64_t s = set;
        while (s){ int b = __builtin_ctzll(s); idx[n++] = b; s &= s-1; }
        memset(s1, 0, sizeof s1); memset(s2, 0, sizeof s2);
        for (int i = 0; i < 10; i++){ zadd(s1, idx[i]); zadd(s2, 2*idx[i]); }
        // sq = s1^2 mod x^16+1
        memset(sq, 0, sizeof sq);
        for (int i = 0; i < 16; i++) if (s1[i])
            for (int j = 0; j < 16; j++) if (s1[j]) sq[i+j] += s1[i]*s1[j];
        int zero = 1;
        for (int t = 0; t < 16; t++){
            int64_t c = sq[t] - (t+16 <= 30 ? sq[t+16] : 0) - s2[t];
            if (c){ zero = 0; break; }
        }
        if (zero){
            count++;
            if (examples < 8){
                printf("SOL:");
                for (int i = 0; i < 10; i++) printf(" %d", idx[i]);
                printf("\n");
                examples++;
            }
        }
        checked++;
        // Gosper next
        uint64_t c2 = set & -set, r = set + c2;
        set = (((r ^ set) >> 2) / c2) | r;
    }
    printf("checked=%lld char0_solutions=%lld\n", checked, count);
    return 0;
}

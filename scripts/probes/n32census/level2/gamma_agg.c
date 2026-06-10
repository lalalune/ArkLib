/* gamma_agg.c — exact aggregation of the exact-17 floor gamma streams (uint32 LE).
 * Usage: ./gagg <queries.txt> <out.txt> <bin1> [bin2 ...]
 * Builds a uint16 saturating count array over [0, 2^31) (gamma < P < 2^31), then emits:
 *   total <emissions read>          (each emission = one distinct (gamma,codeword) pair
 *                                    at agreement exactly 17 — bijection proved in postpass)
 *   distinct <slots with count>0>
 *   max <max count>   sat <slots that hit 65535>
 *   hist <count> <ngammas>          for every count value present
 *   q <gamma> <count>               for each query gamma (the agree>=18 record gammas)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define SLOTS (1ULL << 31)

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s <queries.txt> <out.txt> <bin...>\n", argv[0]); return 2; }
    uint16_t *cnt = calloc(SLOTS, 2);
    if (!cnt) { fprintf(stderr, "calloc 4GiB failed\n"); return 2; }
    uint64_t total = 0, sat = 0;
    static uint32_t buf[1 << 22];
    for (int f = 3; f < argc; f++) {
        FILE *fp = fopen(argv[f], "rb");
        if (!fp) { perror(argv[f]); return 2; }
        size_t n;
        while ((n = fread(buf, 4, 1 << 22, fp)) > 0) {
            total += n;
            for (size_t i = 0; i < n; i++) {
                uint32_t g = buf[i];
                if (g >= SLOTS) { fprintf(stderr, "gamma out of range\n"); return 2; }
                if (cnt[g] == 65535) sat++; else cnt[g]++;
            }
        }
        fclose(fp);
    }
    uint64_t hist[65536] = {0};
    uint64_t distinct = 0; uint32_t maxc = 0;
    for (uint64_t g = 0; g < SLOTS; g++) {
        uint16_t c = cnt[g];
        if (c) { distinct++; hist[c]++; if (c > maxc) maxc = c; }
    }
    FILE *out = fopen(argv[2], "w");
    if (!out) { perror("out"); return 2; }
    fprintf(out, "total %llu\ndistinct %llu\nmax %u\nsat %llu\n",
            (unsigned long long)total, (unsigned long long)distinct, maxc, (unsigned long long)sat);
    for (uint32_t c = 1; c <= maxc; c++)
        if (hist[c]) fprintf(out, "hist %u %llu\n", c, (unsigned long long)hist[c]);
    FILE *qf = fopen(argv[1], "r");
    if (qf) {
        unsigned long long q;
        while (fscanf(qf, "%llu", &q) == 1)
            fprintf(out, "q %llu %u\n", q, q < SLOTS ? cnt[q] : 0);
        fclose(qf);
    }
    fclose(out);
    return 0;
}

/* climb2.c — climb.c with GREEDY SPREAD initialization (for high-r hunts).
 * Identical state/cost/moves/output to climb.c; the only change: each
 * restart builds O' greedily — fibers added one at a time, each chosen as
 * the best of K random candidates by incremental cost — instead of uniform
 * random. Sign bits also greedily chosen per added fiber.
 * HIT lines identical; verify with verify_hit.py / numeric_check.py.
 * args: s r seed nrestarts maxsteps [maxhits] [K]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static uint64_t rs;
static uint64_t rnd(void) {
    uint64_t z = (rs += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static int S, N, A, R, Bsz, M;
static int O[40];
static long m_;
static int par;
static int RCUR;   /* current #fibers during greedy build */

static int forced[600], freeax[600], nf, nva, hh;
static int evalcost_r(int rr) {
    static int cnt[1100], inO[1100];
    int a[40];
    a[0] = O[0];
    for (int i = 1; i < rr; i++) a[i] = O[i] + S * ((m_ >> (i - 1)) & 1);
    memset(cnt, 0, sizeof(int) * N);
    for (int i = 0; i < rr; i++)
        for (int j = i + 1; j < rr; j++)
            cnt[(a[i] + a[j]) % N]++;
    for (int i = 0; i < rr; i++) cnt[(2 * O[i]) % N]++;
    cnt[(3 * S / 2) % N]++;
    memset(inO, 0, sizeof(int) * S);
    for (int i = 0; i < rr; i++) inO[O[i]] = 1;
    int cost = 0, D = 0;
    nf = nva = 0;
    for (int c = 0; c < A; c++) {
        int d = cnt[2 * c] - cnt[2 * c + S];
        int ad = d < 0 ? -d : d;
        D += ad;
        if (ad > 1) cost += ad - 1;
        else if (ad == 1) {
            int ff = (d == -1) ? c : c + A;
            if (inO[ff]) cost += 1; else forced[nf++] = ff;
        } else {
            if (!inO[c] && !inO[c + A]) freeax[nva++] = c;
        }
    }
    hh = D;
    if (D > Bsz) cost += D - Bsz;
    return cost;
}
static int evalcost(void) { return evalcost_r(R); }

static int inuse(int x, int upto) {
    for (int t = 0; t < upto; t++) if (O[t] == x) return 1;
    return 0;
}

int main(int argc, char **argv) {
    S = atoi(argv[1]); R = atoi(argv[2]);
    rs = strtoull(argv[3], 0, 10);
    long long NRST = atoll(argv[4]), MAXST = atoll(argv[5]);
    long long maxhits = argc > 6 ? atoll(argv[6]) : 5, hits = 0;
    int K = argc > 7 ? atoi(argv[7]) : 24;
    N = 2 * S; A = S / 2; Bsz = (S + 1 - R) / 2; M = S / 2;
    int bestglobal = 1 << 30;
    for (long long rst = 0; rst < NRST && hits < maxhits; rst++) {
        par = rnd() & 1;
        m_ = 0;
        /* greedy build */
        O[0] = 2 * (rnd() % M) + par;
        for (int k = 1; k < R; k++) {
            int bestx = -1, bestm = 0, bestc = 1 << 30;
            for (int t = 0; t < K; t++) {
                int x;
                do { x = 2 * (rnd() % M) + par; } while (inuse(x, k));
                O[k] = x;
                for (int mb = 0; mb < 2; mb++) {
                    long sv = m_;
                    if (mb) m_ |= (1L << (k - 1)); else m_ &= ~(1L << (k - 1));
                    int c = evalcost_r(k + 1);
                    if (c < bestc) { bestc = c; bestx = x; bestm = mb; }
                    m_ = sv;
                }
            }
            O[k] = bestx;
            if (bestm) m_ |= (1L << (k - 1)); else m_ &= ~(1L << (k - 1));
        }
        int cost = evalcost();
        for (long long st = 0; st < MAXST && cost > 0; st++) {
            int kind = rnd() % 3;
            int io = 0, oldo = 0; long oldm = m_;
            if (kind == 0) {
                int i = 1 + rnd() % (R - 1);
                m_ ^= (1L << (i - 1));
            } else {
                io = rnd() % R; oldo = O[io];
                int x, ok2 = 0, tries = 0;
                do {
                    x = 2 * (rnd() % M) + par;
                    ok2 = !inuse(x, R);
                } while (!ok2 && ++tries < 50);
                if (!ok2) continue;
                O[io] = x;
            }
            int nc = evalcost();
            int dT = nc - cost;
            if (dT <= 0 || (rnd() % 1000) < (dT == 1 ? 60 : (dT == 2 ? 6 : 0))) {
                cost = nc;
            } else {
                if (kind == 0) m_ = oldm; else O[io] = oldo;
            }
        }
        if (cost < bestglobal) bestglobal = cost;
        if (cost == 0) {
            evalcost();   /* refresh forced/freeax/hh */
            int kk = (Bsz - hh) / 2;
            if ((Bsz - hh) & 1) { printf("PARITY_VIOLATION\n"); continue; }
            if (kk > nva) continue;
            hits++;
            printf("HIT s %d r %d | O", S, R);
            for (int i = 0; i < R; i++) printf(" %d", O[i]);
            printf(" | m %ld | B", m_);
            for (int i = 0; i < nf; i++) printf(" %d", forced[i]);
            for (int i = 0; i < kk; i++) printf(" %d %d", freeax[i], freeax[i] + A);
            printf("\n");
            fflush(stdout);
        }
    }
    printf("CLIMB2 s %d r %d b %d restarts %lld hits %lld bestcost %d\n",
           S, R, Bsz, NRST, hits, bestglobal);
    return 0;
}

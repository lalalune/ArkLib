#!/usr/bin/env python3
"""Refutation probe for the mean-degree law (issue #389).

THE MEAN-DEGREE LAW (issue-thread conjecture): for every word w, the capped
large-agreement family {c in RS[q,n,k] : t <= |agree(c,w)| <= cap} satisfies
  Sum_c |agree(c,w)| <= 2n.

This probe shows the law is FALSE below Johnson at q = Theta(n), fixed t:
a RANDOM word over the full domain n = q has ~ q^2 * C(n,t)/q^t lines of
agreement >= t, hence Sum a_c ~ t*C(n,t)/q^(t-2) = Theta(n^2) -- the
quadratic set-system optimum is realized by random words once n^3 >~ t!*q^2.
The census probes (n <= 20, q = 31) sat just below that visibility threshold.

Output (k=2, t=4, cap=6, full domain n=q):
  q=n=17: 2n=34  avg ~17   best(random, globally 5-capped) 30   -- law holds
  q=n=19: 2n=38  avg ~24   best 45 > 38                          -- VIOLATED
  q=n=23: 2n=46  avg ~36   best 51 > 46                          -- VIOLATED
  q=n=31: 2n=62  avg ~69 (AVERAGE word violates)  best 85        -- VIOLATED

The q=n=19 witness (hardcoded in MeanDegreeLawRefuted.lean, with a 10-line
subfamily summing to 41 > 38, word globally capped at 5):
  w = [3,10,14,10,1,14,16,13,15,2,6,16,8,2,14,8,17,14,1]
"""
import random

def run(q, n, t=4, cap=6, trials=60, seed=7):
    random.seed(seed)
    best = None
    tot_sum = 0
    for _ in range(trials):
        w = [random.randrange(q) for _ in range(n)]
        fam = []
        mx = 0
        for a in range(q):
            for b in range(q):
                cnt = sum(1 for x in range(n) if (a * x + b) % q == w[x])
                mx = max(mx, cnt)
                if t <= cnt <= cap:
                    fam.append((a, b, cnt))
        tot = sum(c for _, _, c in fam)
        tot_sum += tot
        if mx <= cap and (best is None or tot > best[0]):
            best = (tot, mx, w, fam)
    return tot_sum / trials, best

if __name__ == "__main__":
    for q in (17, 19, 23, 31):
        avg, best = run(q, q)
        status = "VIOLATED" if best[0] > 2 * q else "holds"
        print(f"q=n={q}: 2n={2*q}  avg Sum a_c={avg:.1f}  "
              f"best (globally {best[1]}-capped) = {best[0]}  -> law {status}")
    # the Lean witness at q=n=19
    q = n = 19
    w = [3, 10, 14, 10, 1, 14, 16, 13, 15, 2, 6, 16, 8, 2, 14, 8, 17, 14, 1]
    fam = []
    mx = 0
    for a in range(q):
        for b in range(q):
            cnt = sum(1 for x in range(n) if (a * x + b) % q == w[x])
            mx = max(mx, cnt)
            if 4 <= cnt <= 6:
                fam.append((a, b, cnt))
    sub = [(15, 3), (0, 14), (2, 3), (2, 4), (3, 1), (4, 4), (5, 5), (5, 13),
           (11, 12), (12, 17)]
    ssum = sum(c for a, b, c in fam if (a, b) in sub)
    print(f"\nLean witness q=n=19: global max agreement = {mx} (<= cap 6), "
          f"full family Sum = {sum(c for _,_,c in fam)}, "
          f"10-line subfamily Sum = {ssum} > 38 = 2n: {ssum > 38}")

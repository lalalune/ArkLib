"""Probe (#444): is E_2(G) <= 3|G|^2  (= GaussianEnergyBound at r=2, the r=1 ERM step
from base E_1=|G|)?  And is it ROBUST for general negation-closed G, or special to mu_n?

E_2(G) := additive energy = #{(x1,x2,y1,y2) in G^4 : x1+x2 = y1+y2}
        = sum_s r(s)^2 where r(s) = #{(a,b) in G^2 : a+b = s}.

(1) mu_n char-0 anchor: closed form E_2 = 3n^2 - 3n  (in-tree REnergyTwoExact).
(2) general negation-closed random sets in Z_p: brute additive energy vs 3|G|^2.
"""
import random
from collections import Counter

print("mu_n char-0: E_2 = 3n^2-3n  vs  3n^2 (GaussianEnergyBound r=2)")
for n in [4, 8, 16, 32, 64]:
    E2 = 3 * n * n - 3 * n
    bound = 3 * n * n
    print("  n=%d: E_2=%d  3n^2=%d  E_2<=3n^2? %s  slack=%d (=3n)"
          % (n, E2, bound, E2 <= bound, bound - E2))

print()
print("general negation-closed random sets in Z_p: E_2 vs 3|G|^2 (is the sharp r=2 bound GENERAL?)")
random.seed(1)
fails = 0
for trial in range(12):
    p = random.choice([101, 211, 307])
    m = random.randint(2, 9)
    base = random.sample(range(1, p), m)
    G = sorted(set([x % p for x in base] + [(-x) % p for x in base]))
    c = Counter()
    for a in G:
        for b in G:
            c[(a + b) % p] += 1
    E2 = sum(v * v for v in c.values())
    nn = len(G)
    ok = E2 <= 3 * nn * nn
    if not ok:
        fails += 1
    print("  |G|=%d: E_2=%d  3|G|^2=%d  E_2<=3|G|^2? %s" % (nn, E2, 3 * nn * nn, ok))
print("general-set FAILS: %d/12  -> sharp r=2 bound is %s for general G"
      % (fails, "NOT universal (mu_n-special)" if fails else "robust here"))

print()
print("structured arithmetic progressions (high additive energy) in Z_p: stress test")
for (p, m) in [(101, 5), (211, 7), (307, 9)]:
    AP = sorted(set([k % p for k in range(m)] + [(-k) % p for k in range(m)]))
    c = Counter()
    for a in AP:
        for b in AP:
            c[(a + b) % p] += 1
    E2 = sum(v * v for v in c.values())
    nn = len(AP)
    print("  AP |G|=%d: E_2=%d  3|G|^2=%d  E_2<=3|G|^2? %s" % (nn, E2, 3 * nn * nn, E2 <= 3 * nn * nn))

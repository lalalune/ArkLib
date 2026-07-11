"""
PROBE (#444 conj #3): the falling-factorial closed form for the CHAR-0 additive energy.

CLAIM A (exactness, char-0): for a GENERIC n-set S (Sidon-like to high order, no nontrivial additive
  coincidences below the permutation level), the 2r-th additive energy
      E_r = #{(a in S^r, b in S^r): sum a = sum b}
  equals
      A_r^{char0} = (2r-1)!! * n^r * prod_{j=1}^{r-1}(1 - j/n).
  Reason (to verify numerically): the matched solutions are partitions of {1..r}x{1..r} into pairs;
  Wick=(2r-1)!! counts the pairings, n^r is the free choice per pair, and prod(1-j/n) is the
  DISTINCTNESS correction (no two pairs land on the same element -- sampling without replacement).

CLAIM B (analytic inequality, fully provable in Lean): for 0<=j<n,  1 - j/n <= exp(-j/n), so
      prod_{j=1}^{r-1}(1 - j/n) <= exp( - sum_{j=1}^{r-1} j/n ) = exp(-r(r-1)/(2n)) <= exp(-(r-1)^2/(2n)).
  i.e. the falling-factorial product is <= the Gaussian-tail factor. This is the RIGOROUS half of the
  machine-found law A_r/Wick ~ exp(-r^2/2n): the falling-factorial IS that factor, bounded cleanly.
"""
from collections import Counter
import math, random

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def falling(n, r):
    p = 1.0
    for j in range(1, r):
        p *= (1 - j / n)
    return p

def char0_energy(S, r):
    # E_r = sum over s of (count of r-tuples summing to s)^2
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[v + x] += m
        c = nc
    return sum(m * m for m in c.values())

print("CHAR-0 additive energy vs Wick*falling-factorial:")
print(f"{'n':>3} {'r':>2} {'E_r(char0)':>14} {'Wick':>14} {'Wick*falling':>16} {'E_r/Wick':>9} {'falling':>9} {'match?':>10}")
random.seed(7)
for n in [8, 12, 16, 20]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    for r in range(2, 7):
        E = char0_energy(S, r)
        W = dfac(r) * n ** r
        fall = falling(n, r)
        Wf = W * fall
        match = "YES" if abs(E - Wf) < 1e-6 * max(1, Wf) else f"off {E/Wf:.4f}"
        print(f"{n:>3} {r:>2} {E:>14} {W:>14} {Wf:>16.1f} {E/W:>9.4f} {fall:>9.4f} {match:>10}")
    print()

print("CLAIM B  prod_{j=1}^{r-1}(1-j/n) <= exp(-r(r-1)/2n):")
allok = True
for n in [16, 32, 64, 256]:
    for r in range(2, n // 2):
        lhs = falling(n, r)
        rhs = math.exp(-r * (r - 1) / (2 * n))
        if not (lhs <= rhs + 1e-12):
            allok = False
            print(f"  VIOLATION n={n} r={r}: {lhs:.6g} > {rhs:.6g}")
print(f"  CLAIM B holds for all tested (n up to 256, r<n/2): {allok}")

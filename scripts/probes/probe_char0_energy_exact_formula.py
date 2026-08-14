"""
PROBE: what IS the exact char-0 additive energy of a generic (Sidon-to-high-order) n-set?

E_r = #{(a,b) in S^r x S^r : sum a = sum b} for GENERIC S.
For generic S the ONLY coincidences sum a = sum b are when the MULTISET {a_1..a_r} = {b_1..b_r}
(no nontrivial linear relations among the elements). So
   E_r = sum over multisets M of size r from S of (number of orderings of M)^2
       = sum_{compositions} (r! / prod mult!)^2  over all multisets.
Equivalently E_r = sum_{lambda partition shape over n symbols} (multinomial)^2.

Key identity to test: E_r = #{(a,b): multiset(a)=multiset(b)} = sum_{f: [r]->S} #{permutations g of [r]: a∘g = a as multiset}... 
Cleaner: E_r = sum_{k-tuples with multiplicities} . Let's just compute and compare to known closed forms:
  (i)  Wick * falling                = (2r-1)!! n^r prod(1-j/n)
  (ii) the 'permanent/matching' count = number of perfect matchings weighted...
  (iii) E_r = r! * [number of ways] ... 
Actually the generic additive energy equals the number of pairs of r-tuples that are PERMUTATIONS of
each other = sum over multisets M (|orbit(M)|)^2 = sum_M (r!/prod_i m_i!)^2.

We compute E_r directly (generic) and ALSO compute T_r := sum over functions f:[r]->[n] of (number of
f' that are a permutation-relabeling)... and compare E_r to:
  - the 'Touchard/Bessel' moment of a uniform-without-replacement?
Let's just tabulate E_r and fit E_r / (n^r) and E_r/(n(n-1)...(n-r+1)) [the strict falling factorial of n].
"""
from collections import Counter
import math, random

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def char0_energy(S, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[v + x] += m
        c = nc
    return sum(m * m for m in c.values())

def perm_energy_formula(n, r):
    # E_r for generic = sum over multisets of size r from n symbols of (r!/prod mult!)^2
    # iterate over partitions of r into at most n parts (the multiplicity profile), multiply by
    # number of ways to assign distinct symbols to the parts.
    # partitions of r:
    def partitions(num, maxpart):
        if num == 0:
            yield []
            return
        for first in range(min(num, maxpart), 0, -1):
            for rest in partitions(num - first, first):
                yield [first] + rest
    total = 0
    for part in partitions(r, r):
        if len(part) > n:
            continue
        # multinomial orderings of a multiset with these multiplicities
        orderings = math.factorial(r)
        for m in part:
            orderings //= math.factorial(m)
        # number of ways to pick which DISTINCT symbols get these multiplicities:
        # choose len(part) distinct symbols from n, but account for equal-multiplicity parts (unordered)
        prof = Counter(part)
        ways = 1
        remaining = n
        # number of distinct symbols used = len(part); assign multiplicities to symbols:
        # = n!/(n-len(part))! / prod over equal-mult groups of (group size)!
        k = len(part)
        ways = math.perm(n, k)
        for cnt in prof.values():
            ways //= math.factorial(cnt)
        total += ways * orderings * orderings
    return total

print("char-0 generic additive energy: direct vs permutation-multiset formula:")
print(f"{'n':>3} {'r':>2} {'E_direct':>14} {'E_formula':>14} {'match':>6} {'E/n^r':>10} {'E/Wick':>9}")
random.seed(11)
for n in [8, 12, 16]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    for r in range(2, 7):
        E = char0_energy(S, r)
        F = perm_energy_formula(n, r)
        print(f"{n:>3} {r:>2} {E:>14} {F:>14} {str(E==F):>6} {E/n**r:>10.3f} {E/(dfac(r)*n**r):>9.4f}")
    print()

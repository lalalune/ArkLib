"""
PROBE: the exact SECOND-order term of the char-0 generic additive energy.

From the exact partition formula (LANE-1, verified):
  E_r = sum_{lambda |- r}  ways(lambda) * orderings(lambda)^2,
where the partition lambda = multiplicity profile, ways = #(distinct-symbol assignments), orderings = r!/prod m_i!.

Leading (lambda = 1^r):            L_r = r! * (n)_r.
Next term (lambda = (2,1^{r-2})):  exactly ONE pair coincides.
  k = r-1 distinct symbols used; one has multiplicity 2, the rest multiplicity 1.
  orderings = r!/2! = r!/2.
  ways = perm(n, r-1) / (1)   [the mult-2 symbol is distinguishable from the mult-1 ones; the (r-2)
         mult-1 symbols are an unordered group of size r-2 -> divide by (r-2)!? No: ways counts assignments
         of DISTINCT symbols to the parts; parts of equal multiplicity are interchangeable.]
  Using the LANE-1 formula: ways = perm(n,k) / prod_g (groupsize!) where groups are by multiplicity.
  For (2,1^{r-2}): groups = {mult2: size 1}, {mult1: size r-2} -> divide by 1! * (r-2)!.
  ways = perm(n, r-1) / ( (r-2)! ).
  term2 = ways * orderings^2 = [perm(n,r-1)/(r-2)!] * (r!/2)^2.

Test: E_r =? L_r + term2 + (higher).  Compute the ratio (E_r - L_r)/term2 -> should be ~1 for large n
(higher terms are lower order in n). And give the exact two-term lower bound E_r >= L_r + term2.
"""
import math, random
from collections import Counter

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def perm(n, k):
    p = 1
    for j in range(k):
        p *= (n - j)
    return p

def char0_energy(S, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[v + x] += m
        c = nc
    return sum(m * m for m in c.values())

def Lr(n, r):
    return math.factorial(r) * perm(n, r)

def term2(n, r):
    # lambda = (2, 1^{r-2}), needs r >= 2
    if r < 2:
        return 0
    orderings = math.factorial(r) // 2
    ways = perm(n, r - 1) // math.factorial(r - 2) if r >= 2 else 0
    return ways * orderings * orderings

print("char-0 energy: leading L_r + second-order term2, and exactness of two-term:")
print(f"{'n':>3} {'r':>2} {'E_r':>14} {'L_r':>14} {'term2':>14} {'(E-L)/term2':>11} {'L+t2<=E?':>9}")
random.seed(13)
for n in [12, 16, 20, 24]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    for r in range(2, 7):
        E = char0_energy(S, r)
        L = Lr(n, r)
        t2 = term2(n, r)
        ratio = (E - L) / t2 if t2 else float('nan')
        twoterm_ok = (L + t2) <= E
        print(f"{n:>3} {r:>2} {E:>14} {L:>14} {t2:>14} {ratio:>11.4f} {str(twoterm_ok):>9}")
    print()
print("=> if (E-L)/term2 -> 1 as n grows, term2 is the exact 2nd-order term; L+t2<=E gives a")
print("   sharper provable lower bound on the char-0 energy than L alone (all partition terms positive).")

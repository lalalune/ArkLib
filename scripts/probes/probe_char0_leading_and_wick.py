"""
PROBE: the leading term of char-0 generic energy, and E_r^char0 <= Wick.

The exact formula E_r^char0 = sum_{partitions lambda of r} N(lambda), where for lambda with parts
m_1>=...>=m_k (k = number of distinct symbols used, sum m_i = r):
   N(lambda) = [ perm(n,k) / prod_g (g!) ] * (r! / prod_i m_i!)^2
   where prod_g g! accounts for groups of equal multiplicities.

Leading term (lambda = 1^r, all distinct): k=r, all m_i=1, group of size r ->
   N = [perm(n,r)/r!] * (r!)^2 = r! * perm(n,r) = r! * n(n-1)...(n-r+1).

So E_r^char0 = r! * fallingfac(n,r) + (lower terms from coincidences).
And r! * fallingfac(n,r) = r! * n^r * prod_{j=0}^{r-1}(1-j/n).

CLAIM C: E_r^char0 <= Wick = (2r-1)!! n^r  for all r<=n. (char-0 sub-Wick -- the FAVORABLE/prize-true direction)
CLAIM D: the LEADING term r!*fallingfac(n,r) <= Wick, i.e. r! * prod_{j=0}^{r-1}(1-j/n) <= (2r-1)!!.
         Since (2r-1)!! = (2r)!/(2^r r!), claim D <=> (r!)^2 prod(1-j/n) <= (2r)!/2^r, i.e.
         prod_{j=1}^{r-1}(1-j/n) <= (2r)!/(2^r (r!)^2) = C(2r,r) r!/(2^r r!) ... let's just test numerically.
"""
import math, random
from collections import Counter

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def fallingfac(n, r):
    p = 1
    for j in range(r):
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

print("CLAIM C: E_r^char0 <= Wick=(2r-1)!! n^r ?   and leading term r!*falling(n,r):")
print(f"{'n':>3} {'r':>2} {'E_char0':>14} {'Wick':>16} {'E<=Wick':>8} {'lead=r!fall':>14} {'lead/E':>7}")
random.seed(3)
allC = True
for n in [8, 12, 16, 20]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    for r in range(2, min(8, n)):
        E = char0_energy(S, r)
        W = dfac(r) * n ** r
        lead = math.factorial(r) * fallingfac(n, r)
        c_ok = E <= W
        if not c_ok:
            allC = False
        print(f"{n:>3} {r:>2} {E:>14} {W:>16} {str(c_ok):>8} {lead:>14} {lead/E:>7.4f}")
    print()
print(f"CLAIM C (E_r^char0 <= Wick) holds for all tested: {allC}")

print()
print("CLAIM D: r! * prod_{j=0}^{r-1}(1-j/n) <= (2r-1)!!  [leading term <= Wick/n^r]:")
allD = True
for n in [16, 32, 64, 128, 256]:
    for r in range(2, n):
        # compare r! * falling(n,r)  vs  (2r-1)!! * n^r   (all integers, exact)
        lhs = math.factorial(r) * fallingfac(n, r)
        rhs = dfac(r) * n ** r
        if not (lhs <= rhs):
            allD = False
            print(f"  VIOLATION n={n} r={r}: {lhs} > {rhs}")
print(f"CLAIM D (r! falling/n^r <= (2r-1)!!) holds for all tested: {allD}")
print("  Note: r! <= (2r-1)!! always (since (2r-1)!!/r! = prod (2j-1)/j >= 1), and falling/n^r <=1,")
print("  so D is IMMEDIATE: r! * (<=1) <= r! <= (2r-1)!!.  Fully provable.")

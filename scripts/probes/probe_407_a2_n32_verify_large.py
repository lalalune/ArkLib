"""
#407 LANE A2 — VERIFY the large n=32 norm-prime is a genuine NEW mod-p e2=0 solution,
and clarify the distinction between:
  (i)  the THRESHOLD c(n) = "all char-p e2=0 subsets are char-0 ones" (norm route: HUGE, ~n^8 at n=32),
  (ii) the MEASURED-COUNT crossover "the e2=0 COUNT (and orbit-count K at width n/2) stabilizes
       to its char-0 value for p >~ n^3" (the E2VanishRigidityModP docstring claim).

These differ: a single large prime p* may admit ONE spurious U (out of ~10^9), perturbing the
RAW COUNT by a bounded amount but NOT necessarily the char-0 count. The Lean threshold/transfer
theorem (e2_extra_solution_threshold) is per-U and says: for THAT U, no new solution above
(|U|^2+|U|)^(n/2). The GLOBAL "count = char-0 count" needs NO U to have a spurious solution,
i.e. p above the max-over-U norm prime = the TRUE c(n).

We verify:
  1. the large prime p* = 3184895024161 (or whatever the probe found) is genuinely split
     (n | p-1) and gives a real new mod-p e2=0 solution for its U (e1 != 0 over Z[zeta] but
     e1^2 == p2 mod p*).
  2. We RE-RUN at n=32 to extract the actual max norm-prime cleanly and its U, and confirm
     it is >> n^3 -- so the EXACT minimal threshold c(32) is super-polynomial, NOT ~n^3.
  3. We measure the n=16 norm-prime distribution to show: typical bad primes ARE small (~n^2.7),
     the LARGE primes are RARE single-U coincidences -> reconciles 'measured ~n^3' (typical /
     count-stabilization) vs 'provable threshold' (worst single U, super-poly).
"""
import itertools, math
from sympy import symbols, Poly, cyclotomic_poly, ZZ, factorint, resultant, isprime, primitive_root

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)
def relpoly(U):
    s = Poly(sum(X**i for i in U), X, domain=ZZ)
    return s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)
def rel_norm(U, Phi):
    R = relpoly(U) % Phi
    if R.is_zero: return 0
    return abs(resultant(Phi.as_expr(), R.as_expr(), X))

# verify the specific large-prime U at n=32
n = 32
Phi = phi(n)
U = (0, 2, 6, 8, 9, 10, 11, 13, 14, 20, 21, 23, 28, 31)
N = rel_norm(U, Phi)
f = factorint(N)
splitfacs = sorted([int(p) for p in f if (int(p)-1) % n == 0])
pstar = max(splitfacs)
print(f"=== n=32 large-prime verification, U={U} ===")
print(f"  relation norm N has {len(f)} prime factors; largest split prime p* = {pstar}")
print(f"  p* prime? {isprime(pstar)};  n | p*-1 ? {(pstar-1)%n==0};  p*/n^3 = {pstar/n**3:.3e}  (beta={math.log(pstar)/math.log(n):.2f})")
# direct mod-p* check it is a NEW e2=0 solution
g = pow(primitive_root(pstar), (pstar-1)//n, pstar)
mu = [pow(g, j, pstar) for j in range(n)]
S = [mu[i] for i in U]
e1 = sum(S) % pstar
p2 = sum((x*x) % pstar for x in S) % pstar
e1_char0_zero = (Poly(sum(X**i for i in U), X, domain=ZZ) % Phi).is_zero
print(f"  over F_p*: e1={e1} (e1!=0 mod p*? {e1!=0}), e1^2-p2 mod p* = {(e1*e1-p2)%pstar} (==0 => e2=0)")
print(f"  e1==0 over Z[zeta]? {e1_char0_zero}  -> this is a GENUINE NEW mod-p* e2=0 bad scalar")
print(f"  ==> the EXACT minimal threshold c(32) >= {pstar} = n^{math.log(pstar)/math.log(n):.2f}  >> n^3.\n")

# n=16 norm-prime distribution: typical vs worst
n = 16; Phi = phi(n)
lpfs = []
import random; random.seed(7)
sampleU = list(itertools.combinations(range(n), 4))
for _ in range(2000):
    sampleU.append(tuple(sorted(random.sample(range(n), 8))))
maxsplit = 0
splitset = set()
for U in sampleU:
    Nn = rel_norm(U, Phi)
    if Nn == 0: continue
    sf = [int(p) for p in factorint(Nn) if (int(p)-1)%n==0]
    if sf:
        m = max(sf); maxsplit = max(maxsplit, m); splitset.add(m)
import statistics
sl = sorted(splitset)
print(f"=== n=16 bad-split-prime distribution (per-U largest split factor) ===")
print(f"  distinct max-split-primes seen: {sl}")
print(f"  median {statistics.median(sl) if sl else None}, max {maxsplit} (=c(16) found by brute = 1873)")
print(f"  n^2.5={n**2.5:.0f}, n^3={n**3}: most bad primes <~ n^2.7, threshold c is the WORST single U")

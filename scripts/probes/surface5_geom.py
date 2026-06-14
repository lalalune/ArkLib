"""
SURFACE 5 — Geometry of Numbers reframing of Q4.

Q4(n,r,p) = E_r(F_p) - E_r^char0  counts pairs of r-tuples (a,b) in mu_n^r whose
char-0 difference alpha = sum zeta^{a_i} - sum zeta^{b_j} is NONZERO in Z[zeta_n]
but VANISHES mod p (alpha in p-ideal).

GEOMETRIC CLAIM:
  alpha lives in the cyclotomic lattice L = Z[zeta_n] ~= Z^d (power basis, d=n/2 for n=2^mu,
  since zeta^{n/2}=-1).  alpha is a ZERO-COEFFICIENT-SUM difference of r-root-sums, so each
  power-basis coordinate c_k of alpha satisfies |c_k| <= 2r  =>  alpha in the box B_{2r} = [-2r,2r]^d.
  Vanishing mod p means alpha lies in the sublattice p*L (when p splits completely, p O = prod p_i,
  but the FULL p-divisibility alpha == 0 mod p in Z[zeta] means alpha in pL = pZ^d).

  *** KEY: Q4 onset (Q4>0) <=> the box B_{2r} contains a NONZERO point of pL <=> 2r >= p
      (the shortest nonzero vector of pL in sup-norm is p*e_1, length p). ***
  This is a Minkowski/geometry-of-numbers statement: pL has successive minima all = p (sup norm),
  det(pL) = p^d. # of pL-points in box [-2r,2r]^d = (2*floor(2r/p)+1)^d.

  THE TRANSFER: the per-frequency carrier needs E_r controlled to depth r ~ ln q = beta ln n.
  Q4>0 requires 2r >= p ~ n^beta, i.e. r >= n^beta/2 >> ln n.  So in the PRIZE regime
  (r ~ ln q << p), the box B_{2r} contains NO nonzero pL point except 0 => Q4 = 0 EXACTLY.

  This is the geometry-of-numbers PROOF that Q4=0 to depth r < p/2 (so E_r = E_r^char0 = Wick),
  hence B^{2r} <= p*E_r = p*Wick to all needed depths, with NO anomalous wrap-around.

We verify:
  (1) Q4 onset r* satisfies 2*r* >= (something ~ p), i.e. the box must reach the p-lattice.
  (2) The minimal "bad alpha" (nonzero, vanishing mod p) has sup-norm coordinates summing toward p.
"""
import itertools, cmath
from collections import Counter
from fractions import Fraction
from math import factorial, log

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

def find_subgroup(p,n):
    def order(a):
        o=1;cur=a%p
        while cur!=1: cur=(cur*a)%p;o+=1
        return o
    prim=next(a for a in range(2,p) if order(a)==p-1)
    gen=pow(prim,(p-1)//n,p);sub=[];cur=1
    for _ in range(n): sub.append(cur);cur=(cur*gen)%p
    return sub

def antidiag(d,r):
    if d==0:
        if r==0: yield ()
        return
    for first in range(r+1):
        for rest in antidiag(d-1,r-first): yield (first,)+rest

def bessel(n,r):
    d=n//2; s=Fraction(0)
    for m in antidiag(d,r):
        prod=Fraction(1)
        for mi in m: prod*=Fraction(1,factorial(mi)**2)
        s+=prod
    return int(factorial(2*r)*s)

def E_r_modp(p,n,r):
    sub=find_subgroup(p,n); cnt=Counter({0:1})
    for _ in range(r):
        new=Counter()
        for s,c in cnt.items():
            for x in sub: new[(s+x)%p]+=c
        cnt=new
    return sum(c*c for c in cnt.values())

print("="*90)
print("CLAIM: Q4 onset r* is governed by 2r >= p (box [-2r,2r]^d reaches lattice pZ^d).")
print("Predicted onset: smallest r with 2r >= p, i.e. r* = ceil(p/2)?  Test vs measured.")
print("(But: the box of an r-sum DIFFERENCE has L1-type constraint sum|c_k|<=2r, the relevant")
print(" SHORTEST nonzero p-vanishing alpha is what matters. Measure the true minimal weight.)")
print("="*90)

# (1) Measure Q4 onset for several (n,p) and compare to p
for n in [4, 8, 16]:
    q3={r:bessel(n,r) for r in range(1,20)}
    primes=[x for x in range(n*n, 200*n) if (x-1)%n==0 and is_prime(x)][:5]
    for p in primes:
        onset=None
        for r in range(1,18):
            if E_r_modp(p,n,r) - q3[r] > 0:
                onset=r; break
        if onset:
            print(f"  n={n:3d} p={p:5d}: Q4 onset r*={onset:2d}   2r*={2*onset:3d}  p={p:5d}  "
                  f"2r*/p={2*onset/p:.3f}  r*/(p/2)={onset/(p/2):.3f}")
        else:
            print(f"  n={n:3d} p={p:5d}: no Q4 onset thru r=17 (2*17={34}<p? {34<p})")

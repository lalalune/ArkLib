"""
The onset r* << p/2 REFUTES the naive 'box reaches pZ^d' picture.  Why?

The right object: alpha = sum_{i<r} zeta^{a_i} - sum_{j<r} zeta^{b_j}, a cyclotomic integer,
NONZERO in Z[zeta_n], but p | alpha *as a cyclotomic integer in the SUBGROUP-RESTRICTED sense*.

BUT WAIT. In E_r_modp we embed mu_n into F_p via a fixed iso mu_n(C) -> mu_n(F_p) (a generator
choice). alpha == 0 in F_p means the IMAGE sum vanishes in F_p. This is NOT 'p divides the
cyclotomic integer alpha in Z[zeta_n]'. It is: alpha mod p_0 = 0 for the SPECIFIC prime p_0 = (p, zeta - g)
above p determined by the embedding zeta -> g (g = chosen n-th root of unity in F_p).

So Q4 counts alpha in a FIXED degree-1 prime p_0 | p (norm p_0 = p since p splits), NOT in pZ[zeta]=
intersection of ALL conjugate primes. The relevant lattice is the IDEAL p_0, which has:
   det(p_0) = N(p_0) = p   (index p in Z[zeta], NOT p^d).
So p_0 is an index-p sublattice of Z^d ~ Z[zeta_n] -- a HYPERPLANE-type lattice, NOT pZ^d.

GEOMETRY OF NUMBERS for the ideal p_0:
  - det(p_0) = p, dimension d = n/2 (well d = phi(n) = n/2).
  - successive minima: lambda_1 ... lambda_d with prod ~ det^{1/d} balance => lambda_1 can be O(p^{1/d})!!
  - A short vector of p_0 of euclidean length ~ p^{1/d} EXISTS by Minkowski (lambda_1 <= sqrt(d) det^{1/d} = sqrt(d) p^{1/d}).
  - alpha = (r-sum) - (r-sum) has euclidean length <= 2 sqrt(r) (sum of 2r unit vectors, each |zeta^k|_emb=1...
    actually in power-basis coords the embedding norm: ||alpha||_2^2 = <alpha,alpha> canonical = sum over
    embeddings |alpha|^2; for alpha=sum of unit roots, each archimedean abs <= 2r, the CANONICAL norm
    ||alpha||^2 = sum_{sigma} |sigma(alpha)|^2.)

  *** So onset r* is when 2*sqrt(r) (canonical length budget of an r-difference) reaches lambda_1(p_0) ~ p^{1/d}.
      Predicts r* ~ (p^{1/d})^2 /4 = p^{2/d}/4.   For d=n/2:  r* ~ p^{2/(n/2)} = p^{4/n}. ***

  Check: n=16 => d=8 => r* ~ p^{4/16}=p^{1/4}. p~300 => p^{1/4}~4.2, /4-ish ~ small => r*~2-3. MATCHES!
        n=8  => d=4 => r* ~ p^{4/8}=p^{1/2}. p~100 => 10, hmm. measured r*~3.
        n=4  => d=2 => r* ~ p^{4/4}=p. p~30 => measured r*~5-6 (so r* ~ sqrt(p)? p=37 sqrt=6.1 MATCH r*=6!)

  Refine the canonical-norm budget below.
"""
import itertools, cmath
from collections import Counter
from fractions import Fraction
from math import factorial, log, sqrt

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

def find_subgroup_gen(p,n):
    def order(a):
        o=1;cur=a%p
        while cur!=1: cur=(cur*a)%p;o+=1
        return o
    prim=next(a for a in range(2,p) if order(a)==p-1)
    g=pow(prim,(p-1)//n,p)   # primitive n-th root in F_p
    return g

# Build the ideal lattice p_0 = (p, zeta - g) explicitly in power basis Z^d, d=n/2 (n=2^mu).
# Z[zeta_n] has power basis 1,zeta,...,zeta^{d-1} with zeta^d = -1 (since n=2^mu, phi=n/2=d, min poly X^d+1).
# alpha = sum c_k zeta^k (k<d).  alpha == 0 mod p_0  <=>  sum c_k g^k == 0 mod p (eval zeta->g).
# So p_0 = { c in Z^d : sum_k c_k g^k == 0 mod p }.  This is the kernel lattice of the map c -> sum c_k g^k mod p.
# det = p (index-p sublattice), lambda_1 = shortest vector.

def lattice_p0_lambda1_sup_and_l2(p,n):
    d=n//2
    g=find_subgroup_gen(p,n)
    gpow=[pow(g,k,p) for k in range(d)]
    # find shortest nonzero c in Z^d with sum c_k gpow_k == 0 mod p, search small box
    best_l2=None; best_sup=None; best_l1=None
    # search box [-R,R]^d for small R; d up to 8 so keep R small
    R = 3 if d<=8 else 1
    for c in itertools.product(range(-R,R+1), repeat=d):
        if all(x==0 for x in c): continue
        if sum(ck*gp for ck,gp in zip(c,gpow)) % p == 0:
            l2=sqrt(sum(x*x for x in c)); sup=max(abs(x) for x in c); l1=sum(abs(x) for x in c)
            if best_l2 is None or l2<best_l2:
                best_l2=l2; best_sup=sup; best_l1=l1; bestc=c
    return best_l2, best_sup, best_l1, (bestc if best_l2 else None)

print("Ideal-lattice p_0 = ker(c -> sum c_k g^k mod p) in Z^d, d=n/2.  det=p.")
print("Minkowski: lambda_1(l2) <= sqrt(d)*p^{1/d}. Shortest vector found in small box:")
print(f"{'n':>4}{'p':>6}{'d':>4}{'lam1_l2':>9}{'sqrt(d)p^1/d':>13}{'lam1_sup':>9}{'lam1_l1':>9}{'shortest c':>26}")
for n in [4,8,16]:
    d=n//2
    primes=[x for x in range(n*n, 80*n) if (x-1)%n==0 and is_prime(x)][:3]
    for p in primes:
        l2,sup,l1,c = lattice_p0_lambda1_sup_and_l2(p,n)
        mink = sqrt(d)*p**(1.0/d)
        cs = str(c) if c else "(none in box)"
        if l2:
            print(f"{n:>4}{p:>6}{d:>4}{l2:>9.2f}{mink:>13.2f}{sup:>9}{l1:>9}{cs:>26}")
        else:
            print(f"{n:>4}{p:>6}{d:>4}{'>R':>9}{mink:>13.2f}")

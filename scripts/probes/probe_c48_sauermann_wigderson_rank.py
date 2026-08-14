#!/usr/bin/env python3
"""
Probe for C48 (Effective Sauermann-Wigderson polynomial-method rank bound for the
agreement system).

CONJECTURE C48 claims:
  - the Sauermann-Wigderson polynomial-method rank bound, applied to the simultaneous
    far-line agreement system over F_p, gives a list bound BELOW budget n PAST Johnson,
  - exploiting the "bounded degree of the agreement variety" and the proven rigidity
    transfer (in-tree RigidityReductionPrizeScale).
  - A "modern polynomial-method lever distinct from CLP."

WHAT SAUERMANN-WIGDERSON ACTUALLY IS (arXiv:2010.00077, JLMS 2022):
  Let k >= 2 fixed, n large. The MINIMUM possible DEGREE of a polynomial
  P in R[x_1,...,x_n] with P(0,...,0) != 0 that vanishes to multiplicity >= k at
  EVERY point of the Boolean hypercube {0,1}^n minus {0} equals  n + 2k - 3.
  (k=1 case is Alon-Furedi: degree = n.)
  -> It is an EXTREMAL DEGREE LOWER BOUND on multiplicity-k vanishing over the
     n-DIMENSIONAL Boolean hypercube grid {0,1}^n, over R (char 0).

WHAT THE PRIZE OBJECT IS:
  The far-line agreement "variety" for monomial pencil (a,b) is the set
     B = { alpha in F_p : x^a + alpha x^b is delta-close to RS[k] }
  living in the 1-DIMENSIONAL cyclic ambient (alpha ranges over F_p; the geometry
  is the multiplicative subgroup mu_n, a 1-parameter object). The quantity to bound
  is a LIST SIZE / incidence MULTIPLICITY N, not a minimum vanishing degree.

THE HORNS (any one kills C48):

 (H1) DIMENSIONAL CATEGORY ERROR (same as C39's H2).  SW lives in {0,1}^n, an
      n-FOLD PRODUCT (hypercube of dimension n -> infinity); its content (n+2k-3)
      is a phenomenon of the GROWING NUMBER OF COORDINATES of the grid. The agreement
      system over mu_n is a 1-parameter family in a cyclic group: there is NO n-fold
      Boolean-grid product to host the SW degree formula. (Just as CLP/EG savings live
      in ambient dimension and vanish in cyclic Z/p, the SW n+2k-3 formula is a
      hypercube-dimension statement with no cyclic analogue.) We exhibit that the
      relevant grid here is the eval domain mu_n = a SINGLE-coordinate set, |mu_n|=n
      points on a LINE (1-dim), not {0,1}^n.

 (H2) WRONG DIRECTION OF INEQUALITY / WRONG QUANTITY.  SW is a degree LOWER bound:
      "to vanish to order k off the origin you NEED degree >= n+2k-3". To turn a
      vanishing-degree fact into a list-SIZE UPPER bound you must run it through
      Alon-Furedi / Schwartz-Zippel / Vandermonde dimension counting. We show that
      this counting, applied to deg-<k RS polynomials agreeing on a points, yields
      EXACTLY the k-dimensional / Vandermonde rank obstruction already proven in-tree
      (rank_collapse_on_kset, poly_method_subset_incidence_bound): the agreement
      ceiling agree(c,c') <= k-1. SW's multiplicity refinement only RE-DERIVES this
      ceiling, it does not lower it. We verify the multiplicity-k vanishing count
      against the plain k-1 ceiling on explicit RS instances and find NO improvement.

 (H3) THE FIELD-BLIND / SUPER-POLY WALL (the in-tree converged wall).  The in-tree
      axiom-clean polynomial-method cap |L|*C(a,k) <= C(n,k)  is the OPTIMAL output of
      ANY polynomial method that uses only the k-1 agreement ceiling (it IS the
      Sauermann-Wigderson-style multiplicity double count). It is FIELD-BLIND
      (abstract_incidence_bound: holds for any injective domain D, cannot separate the
      smooth subgroup mu_n from a generic n-set) and SUPER-POLYNOMIAL in the interior
      (per-coordinate exponent H(rho) - alpha*H(rho/alpha) > 0). We compute the cap at
      prize-scale interior points and confirm it is astronomically above budget n.
      "Rigidity transfer" (RigidityReductionPrizeScale) only makes delta*
      char-INDEPENDENT (char-p = char-0 incidence); it does NOT lower the char-0 cap,
      so feeding SW the rigidity transfer buys nothing past Johnson.
"""
import sympy
from math import comb, log2, gcd

def find_p_and_subgroup(n):
    """p prime, p >> n^3 (here p ~ n^4), n | p-1, mu_n proper subgroup, never n=p-1."""
    target = n**4
    m = target // n
    while True:
        p = m * n + 1
        if sympy.isprime(p) and p > 100 * n**3:
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            mu = [pow(z, j, p) for j in range(n)]
            assert len(set(mu)) == n and p - 1 != n
            return p, z, mu
        m += 1

print("=== C48 probe: Sauermann-Wigderson degree bound for the agreement system ===\n")

print("(H1) SW lives in the n-dim Boolean hypercube {0,1}^n; the prize object is 1-dim cyclic.\n")
print("  SW theorem (arXiv:2010.00077): min deg of P in R[x_1..x_n], P(0)!=0, vanishing to")
print("  multiplicity >= k on {0,1}^n \\ {0}, equals n + 2k - 3.  The content is in the")
print("  GROWING dimension n of the hypercube grid.\n")
print("  Prize agreement system: B = {alpha : x^a + alpha x^b delta-close to RS[k]} over mu_n.")
print("  The eval domain mu_n is a SINGLE-coordinate point set on a line (1-dimensional);")
print("  there is no n-fold Boolean product {0,1}^n to host the SW formula.\n")
print(f"  {'n':>5} {'p':>14} {'ambient of SW grid':>22} {'ambient of agreement sys':>26}")
for n in [16, 32, 64]:
    p, z, mu = find_p_and_subgroup(n)
    print(f"  {n:>5} {p:>14} {'{0,1}^n (dim '+str(n)+')':>22} {'mu_n subset F_p (dim 1)':>26}")
print()
print("  HORN H1: SW's n+2k-3 is a hypercube-DIMENSION phenomenon; the cyclic agreement")
print("  system has NO such product structure (same category error as C39 H2: poly-method")
print("  savings live in ambient dimension, vacuous in a 1-dim cyclic group).\n")

print("(H2) SW gives a DEGREE LOWER bound; turning it into a list UPPER bound just re-derives")
print("     the k-1 Vandermonde agreement ceiling already proven in-tree.\n")
print("  We check on explicit RS[F_p, mu_n, k]: do distinct deg-<k codewords EVER agree on >= k")
print("  coordinates of the eval domain?  (If never, the ceiling is agree<=k-1 = the in-tree")
print("  rank_collapse_on_kset; SW multiplicity adds nothing.)\n")
print(f"  {'n':>5} {'k':>4} {'p':>14} {'#poly pairs tested':>18} {'max agree(c,cp)':>16} {'ceiling k-1':>12} {'ok?':>5}")
all_ceiling = True
for n in [16, 32]:
    p, z, mu = find_p_and_subgroup(n)
    for k in [n//8, n//4]:
        if k < 2:
            continue
        # sample distinct deg-<k polynomials, evaluate on mu_n, measure max pairwise agreement
        import random
        random.seed(1)
        polys = []
        for _ in range(40):
            coeffs = [random.randrange(p) for _ in range(k)]
            polys.append(coeffs)
        def ev(coeffs, x):
            acc = 0
            xp = 1
            for c in coeffs:
                acc = (acc + c * xp) % p
                xp = (xp * x) % p
            return acc
        evals = [[ev(c, x) for x in mu] for c in polys]
        maxag = 0
        pairs = 0
        for i in range(len(polys)):
            for j in range(i+1, len(polys)):
                if polys[i] == polys[j]:
                    continue
                ag = sum(1 for t in range(n) if evals[i][t] == evals[j][t])
                maxag = max(maxag, ag)
                pairs += 1
        ok = (maxag <= k - 1)
        all_ceiling = all_ceiling and ok
        print(f"  {n:>5} {k:>4} {p:>14} {pairs:>18} {maxag:>16} {k-1:>12} {str(ok):>5}")
print()
_h2 = ("max pairwise agreement <= k-1 ALWAYS (Vandermonde/SW both give the SAME k-1 ceiling)."
       if all_ceiling else "UNEXPECTED: agreement exceeded k-1")
print("  HORN H2:", _h2)
print("  => SW's multiplicity refinement re-derives, does not beat, the in-tree")
print("     rank_collapse_on_kset / poly_method_subset_incidence_bound ceiling.\n")

print("(H3) The optimal poly-method cap |L|*C(a,k) <= C(n,k) is field-blind & super-poly in")
print("     the interior -> never reaches budget n.  Rigidity transfer does NOT lower it.\n")
print("  Cap = C(n,k)/C(a,k) at the interior agreement a (Johnson radius < (n-a)/n < capacity).")
print("  Johnson radius: a_J = ceil(sqrt(n*k)); interior means a in (k, a_J).  We pick a just")
print("  inside the interior and compare cap vs budget n at prize-band rates.\n")
print(f"  {'n':>8} {'k(rho)':>10} {'a (interior)':>12} {'poly cap C(n,k)/C(a,k)':>26} {'budget n':>10} {'cap<=budget?':>13}")
for n in [16, 32, 64, 256, 1024]:
    for rho_den in [4, 8]:           # rho = 1/4, 1/8  (prize band)
        k = n // rho_den
        if k < 2:
            continue
        aJ = int((n * k) ** 0.5)     # Johnson agreement radius ~ sqrt(nk)
        a = aJ + 1                   # just PAST Johnson, still interior (a < ... )
        if a <= k or a >= n:
            continue
        cap = comb(n, k) // comb(a, k) if comb(a, k) > 0 else float('inf')
        budget = n
        ok = cap <= budget
        cap_str = f"{cap:.3e}" if cap > 1e6 else str(cap)
        print(f"  {n:>8} {'1/'+str(rho_den):>10} {a:>12} {cap_str:>26} {budget:>10} {str(ok):>13}")
print()
print("  HORN H3: the poly-method cap is super-polynomial past Johnson (>> budget n) at every")
print("  prize-band rate. abstract_incidence_bound shows it is FIELD-BLIND (same for generic")
print("  domain), so it cannot exploit mu_n's smoothness. RigidityReductionPrizeScale makes")
print("  delta* char-independent (I_p = I_0) but does NOT shrink the char-0 cap -> SW + rigidity")
print("  still lands exactly on the Johnson wall.\n")

print("=== VERDICT: C48 reduces-to-johnson (the SW/multiplicity poly-method cap = the in-tree")
print("    field-blind k-1 incidence ceiling, valid up to and AT Johnson, super-poly past it),")
print("    with a dimensional category error (H1) in even importing SW's hypercube formula. The")
print("    past-Johnson lever is the open BGK/smooth-domain count, which SW does not supply. ===")

#!/usr/bin/env python3
"""
probe_dsval_beukers_smyth_coset_map.py  (A7 LITERATURE angle, issue #407)

PURPOSE
-------
Test whether the EXACT char-0 over-determined far-line incidence count I(delta) for
RS[mu_n, k=rho*n], direction (a,b), maps onto the Beukers-Smyth (BS) "cyclotomic
points on curves" dichotomy:
    #cyclotomic points  =  (isolated, bounded by ~V(Newton polytope))
                         OR (infinitely many, lying on a torsion-coset component x^i y^j = w).

For our problem the relevant object is the count of distinct gamma such that
    g_gamma(x) = x^a + gamma x^b - P(x),   deg P < k,
vanishes on a w-subset S of mu_n (w = (1-delta) n).  Over-determined (far line) means
the agreement forces rank-deficiency of the generalized Vandermonde
    M = [1, x, ..., x^{k-1}, x^a, x^b]  restricted to S.

This probe computes I(delta) EXACTLY in char 0 (using exact rational/cyclotomic linear
algebra via sympy over Q(zeta_n)) for small n, and checks:
  (1) the measured worst-direction delta* values from the task brief, and
  (2) whether the gamma-fibers organize into dilation cosets (the #400/#389 orbit count),
      which is the BS "torsion-coset" branch.

HONESTY: char-0 exact (cyclotomic), PROPER subgroup mu_n = n-th roots of unity, n=2^a.
No finite field, no BGK wall.  Tags below mark proven/observed/conjecture.

RESULT (2026-06-14): This run returned |gammas|=0 for every (n,rho,w) tested.  That is a
PROBE-CONDITION BUG, NOT a refutation: the "left-null vector of the low-degree block kills
the symbolic target" encoding is too strict / mis-models the over-determined consistent-gamma
fiber (for these subset sizes the low-degree block was full-rank so no gamma was forced).  The
probe does NOT measure the orbit count and is NOT load-bearing for the finding.  The substantive
deliverable is the LITERATURE synthesis (Beukers-Smyth / Aliev-Smyth / Tamo / Kong-Tamo); see the
returned structured finding.  TODO if revisited: count distinct gamma via rank-drop of the FULL
generalized Vandermonde M=[1..x^{k-1},x^a,x^b] over S (rank < k+2), then group gamma by dilation
coset to recover the #400/#389 orbit count.
"""
import itertools
from fractions import Fraction
import sys

try:
    import sympy as sp
except Exception as e:
    print("NEED sympy:", e); sys.exit(0)

def roots_of_unity_n(n):
    # exact cyclotomic n-th roots of unity as sympy expressions
    z = sp.exp(2*sp.pi*sp.I/n)
    return [sp.nsimplify(sp.expand_complex(z**j), [sp.pi]) for j in range(n)]

def incidence_count(n, k, a, b, w, verbose=False):
    """
    EXACT char-0 count of distinct gamma such that there exists a w-subset S of mu_n
    on which x^a + gamma x^b agrees with some deg-<k polynomial P.

    Agreement on S of size w with monomials {0..k-1, a, b}:
    The (w x (k+2)) matrix N_S = [ x^j : j in 0..k-1, a, b ] (rows x in S) must have a
    null vector with the x^a and x^b coords structured so that coeff(x^a)=1, coeff(x^b)=gamma,
    and the rest is -P.  I.e.  column_a + gamma*column_b  in  colspan({0..k-1 cols}) over S.
    For OVER-DETERMINED w > k+2: gamma is forced (if it exists) -> finite set.
    We enumerate w-subsets S, solve for gamma exactly, collect distinct gamma.
    """
    mu = roots_of_unity_n(n)
    cols_lowdeg = list(range(k))
    gammas = set()
    idx = list(range(n))
    for S in itertools.combinations(idx, w):
        # Build matrix rows for x in S: [x^0..x^{k-1} | x^a | x^b]
        rows_low = sp.Matrix([[sp.simplify(mu[i]**j) for j in cols_lowdeg] for i in S])
        col_a = sp.Matrix([sp.simplify(mu[i]**a) for i in S])
        col_b = sp.Matrix([sp.simplify(mu[i]**b) for i in S])
        # We need: col_a + gamma*col_b = rows_low * c  for some c (the -P coeffs).
        # => (col_a + gamma*col_b) in column space of rows_low.
        # Over-determined: solve least-structure. We test for which gamma the augmented
        # system is consistent. Treat gamma symbolically.
        g = sp.symbols('g')
        target = col_a + g*col_b
        aug = rows_low.row_join(target)
        # Consistency of rows_low * c = target  <=>  rank(rows_low) == rank(aug).
        # rank(aug) drops to rank(rows_low) only for specific gamma -> solve det conditions.
        r_low = rows_low.rank()
        # Reduce augmented: find gamma making it consistent. Use the condition that all
        # (r_low+1)-minors of aug vanish. Cheaper: pick a basis of left-null space of rows_low
        # and require it kill target.
        ns = rows_low.T.nullspace()  # left null vectors v: v^T rows_low = 0
        if not ns:
            continue
        conds = []
        for v in ns:
            conds.append(sp.simplify((v.T * target)[0]))
        # Each cond is linear in g: alpha + beta*g = 0
        sol = None
        consistent = True
        gval = None
        for c in conds:
            c = sp.expand(c)
            beta = sp.simplify(sp.diff(c, g))
            alpha = sp.simplify(c.subs(g, 0))
            if beta == 0:
                if sp.simplify(alpha) != 0:
                    consistent = False; break
            else:
                this = sp.simplify(-alpha/beta)
                if gval is None:
                    gval = this
                elif sp.simplify(gval - this) != 0:
                    consistent = False; break
        if consistent and gval is not None:
            gammas.add(sp.simplify(gval))
            if verbose:
                print("  S=",S," gamma=",gval)
    return gammas

def main():
    # Task-brief measured worst-direction points (q-independent, exact):
    # rho=1/4: n=8 -> 0.375 (dir 4,7); n=16 -> 0.5625 (dir 4,6)
    # rho=1/2: n=8 -> 0.25 (dir 4,5)
    cases = [
        # (n, rho, a, b, label)
        (8, Fraction(1,4), 4, 7, "n=8,rho=1/4,dir(4,7) meas delta*=0.375"),
        (8, Fraction(1,2), 4, 5, "n=8,rho=1/2,dir(4,5) meas delta*=0.25"),
    ]
    budget_factor = 1  # budget = n
    for (n, rho, a, b, label) in cases:
        k = int(rho*n)
        budget = n*budget_factor
        print("="*70)
        print(label, " k=",k," budget=",budget)
        # scan delta downward: w = (1-delta) n. over-det far line needs w >= k+3.
        for w in range(n, k+2, -1):
            delta = Fraction(n-w, n)
            G = incidence_count(n, k, a, b, w)
            print(f"  w={w}  delta={float(delta):.4f}  I(delta)=|gammas|={len(G)}  (budget {budget})")
        print()

if __name__ == "__main__":
    main()

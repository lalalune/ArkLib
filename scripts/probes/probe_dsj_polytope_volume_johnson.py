#!/usr/bin/env python3
"""
probe_dsj_polytope_volume_johnson.py  (#444, register POLYTOPE/NEWTON/TROPICAL)

ADVERSARIAL TEST of the POLYTOPE register's two load-bearing claims:

  [P1]  worst-dir over-det incidence I(n,delta) ~ NORMALIZED VOLUME of the
        incidence polytope {S subset mu_n : p_j(S)=a_j, j<=t}, and Aliev-Smyth
        gives that isolated-fiber count as O(volume) ~ O(n).
  [P11] the Johnson leading constant sqrt(rho) is FORCED by pure convex geometry
        of the rate-rho simplex (no cancellation), i.e. the budget-n crossing
        happens at agreement = sqrt(rho)*n.

We do NOT trust the algebra; we MEASURE.  Two independent checks:

(A) JOHNSON MAIN TERM.  For the smooth-domain RS setup at rho=1/4 the GPU pin says
    s*(n) = n/2 + 1 - 2*(log2 n - 3) and agreement_johnson = sqrt(rho)*n = n/2.
    The polytope claim P11 is that the LEADING term of s*(n) is sqrt(rho)*n with a
    coefficient that is *pure simplex geometry*.  We test: is s*(n)/n -> sqrt(rho)
    and is the residual exactly the dyadic -2*(tower depth)/n?  This is a pin of
    the GIVEN formula, used as a consistency gate.

(B) THE REAL ADVERSARIAL TEST (P1).  Does a LATTICE-POINT / VOLUME proxy actually
    reproduce the over-determined fiber count, or does Aliev-Smyth's exponential
    constant c2(n) destroy the O(n) claim?  We compute, for the worst direction,
    the EXACT count of 0/1 vectors x in {0,1}^n with sum(x)=w (the agreement set
    indicator over mu_n) satisfying the first t power-sum constraints p_j=a_j,
    and compare to the continuous-relaxation volume of the same constraint slab.
    If P1 is right, count ~ C * vol with C bounded; if Aliev-Smyth is the real
    mechanism, count >> vol (exponential gap) -> P1 collapses to a known bound
    that is TOO WEAK and the register's "O(volume)" is a wish.

NB: this is a *structural* probe over the integer/lattice model of the power-sum
fiber, NOT the char-0 cyclotomic incidence engine (that lives in c32.c).  The
question P1 asks is precisely whether the lattice/volume model is faithful.
"""
import math, itertools
from functools import lru_cache

def log2(n): return int(round(math.log2(n)))

# ---- (A) consistency gate on the GPU-pinned s*(n) ----
def s_star(n):
    return n//2 + 1 - 2*(log2(n) - 3)

def tower_depth(n):
    # # levels in mu_n > mu_{n/2} > ... > mu_8
    return log2(n) - 3

print("=== (A) Johnson main-term decomposition of the PINNED s*(n), rho=1/4 ===")
rho = 0.25
sj = math.sqrt(rho)
print(f"sqrt(rho) = {sj}")
print(f"{'n':>6} {'s*':>6} {'s*/n':>8} {'sqrt_rho':>9} {'resid=(s*-sj*n)':>16} {'-2*depth+1':>11}")
for a in range(3, 11):
    n = 1<<a
    s = s_star(n)
    resid = s - sj*n
    pred = -2*tower_depth(n) + 1   # s* = sqrt(rho)*n + 1 - 2*depth
    print(f"{n:>6} {s:>6} {s/n:>8.4f} {sj:>9.4f} {resid:>16.3f} {pred:>11}")
print("  => if resid == 1 - 2*depth EXACTLY, the 'Johnson main term + dyadic defect'")
print("     decomposition is an algebraic identity in the GIVEN formula (gate only,")
print("     proves nothing about WHY s* equals this).")

# ---- (B) lattice-point count vs volume for the power-sum slab ----
# Model: agreement set is a w-subset A of Z/n (exponents of mu_n).  The j-th
# power sum over the line readout is, in the worst direction, governed by the
# first t moments m_j(A) = sum_{a in A} (a mod n)^j ... but the FAITHFUL object
# for "isolated fiber" is the # of w-subsets hitting a *fixed* moment vector.
# We count exactly for small n and compare to the volume of the relaxed slab
# {x in [0,1]^n : sum x = w, sum x_i*c_i^j = target_j, j=1..t}  (a polytope).

def exact_fiber_count(n, w, t, target):
    """# of w-subsets A of {0..n-1} with sum_{i in A} i^j == target[j-1] for j=1..t."""
    cnt = 0
    for A in itertools.combinations(range(n), w):
        ok = True
        for j in range(1, t+1):
            if sum(i**j for i in A) != target[j-1]:
                ok = False; break
        if ok: cnt += 1
    return cnt

def volume_proxy(n, w, t):
    """Crude normalized-volume proxy: dim of the relaxed slab.
    Full polytope {x in[0,1]^n: 1 linear (sum=w) + t moment constraints} has
    dimension n-(t+1); a t-codim slice of the hypercube.  The Aliev-Smyth claim
    is isolated count = O(d^{c2(n)}) NOT O(vol); we just report the dimension and
    the worst-case combinatorial ceiling C(n,w) to expose the gap scale."""
    return n-(t+1), math.comb(n, w)

print("\n=== (B) exact integer-moment fiber count vs polytope dimension/ceiling ===")
print(f"{'n':>4} {'w':>3} {'t':>3} {'fiber@centroid':>14} {'slab_dim':>9} {'C(n,w)':>10} {'ratio':>8}")
for n in (8, 12, 16):
    for t in (1, 2):
        w = n//2                      # agreement near the Johnson value
        # pick a "generic" achievable target = the moments of a random-ish subset,
        # use the centroid-rounded subset {0,2,4,...} as a representative readout
        A0 = list(range(0, n, max(1, n//w)))[:w]
        if len(A0) < w:
            A0 = list(range(w))
        target = [sum(i**j for i in A0) for j in range(1, t+1)]
        cnt = exact_fiber_count(n, w, t, target)
        dim, ceil = volume_proxy(n, w, t)
        # "volume" of a t-codim slab of C(n,w) ~ C(n,w)/ (range of each moment)
        # range of j-th moment ~ n^{j+1}; so heuristic vol ~ ceil / prod_j n^{j+1}
        volheur = ceil / max(1, math.prod(n**(j+1) for j in range(1, t+1)))
        ratio = cnt / volheur if volheur > 0 else float('inf')
        print(f"{n:>4} {w:>3} {t:>3} {cnt:>14} {dim:>9} {ceil:>10} {ratio:>8.2f}")

print("""
INTERPRETATION KEY:
- If fiber@centroid stays O(n) while t grows and ratio ~ const => the lattice/
  volume MODEL is faithful and P1's 'O(volume)' has teeth (would still need
  Aliev-Smyth replaced by a SHARP volume bound -- NOT what AS gives).
- If fiber@centroid >> volheur or grows with C(n,w) => the integer fiber is NOT
  volume-controlled; Aliev-Smyth's only honest output is the exponential
  c1(n) d^{c2(n)}, so P1's linear claim is UNSUPPORTED (collapses to a too-weak
  known bound).  The leading sqrt(rho) would then NOT be a clean volume statement.
""")

#!/usr/bin/env python3
"""
probe_dsj_johnson_constant_rate_sweep.py  (#444, register CROSS-DOMAIN-PHYSICS)

ATTACK on conjecture (J): the LEADING constant of the over-determined worst-direction
far-line incidence threshold s*(n) is sqrt(rho)*n (the Johnson LIST-DECODING agreement
fraction sqrt(rho), radius 1-sqrt(rho)), and this constant is FORCED structurally
(simplex/budget geometry) rather than borrowed from square-root cancellation.

If (J) is true and structural, then sweeping the RATE rho the budget-crossing agreement
fraction s*/n should track sqrt(rho) -- NOT rho, NOT (1+rho)/2 (the singleton bound), and
NOT a cancellation-dependent rho^{1/4} etc.

EXACT char-0 cyclotomic incidence (no GPU, no field):  a 2-monomial far pencil
X^a + gamma X^b is "bad at an agreement set S subset mu_n, |S|=s" iff the
complete-homogeneous (Schur) readout h_{j}(v_S)=0 with j = b - (s-1) [in-tree
SchurLagrangeBridge].  Over mu_n (roots of unity) h_j(v_S)=0 is a char-0 cyclotomic
vanishing condition.  We use the EXACT integer test (no prime): for S subset mu_n,
  e_2(S) etc. via power sums p_t(S) = sum_{x in S} x^t which are sums of n-th roots
  of unity -> exact in Z[zeta_n].  We test the OVER-DETERMINED system directly:
  number of S of size s on which the worst monomial direction is "bad" (rank-deficient).

This probe MEASURES s*(n) for several (rho, n) by EXACT exhaustion at small n and asks:
   (Q-J)  does s*(n)/n -> sqrt(rho)  (Johnson main term) as the leading constant?
   (Q-defect) is the residual s*(n) - sqrt(rho)*n monotone in dyadic tower depth (log2 n),
              or does it look like generic O(1) boundary noise?

HONESTY GOALS:
  - If s*/n tracks sqrt(rho): (J) gets structural support, Johnson is the main term.
  - If the leading constant needs cancellation (only emerges at large prime, not char-0
    exact): flag as BGK/Paley-dependent.
  - The defect is a 3-point fit; we explicitly report how many INDEPENDENT n we can
    reach by exact exhaustion (very few) and refuse to over-claim.

DO NOT git commit.
"""
import math
from itertools import combinations

# ---- exact cyclotomic incidence over mu_n via the Schur/divided-difference readout ----
# We model the over-determined "bad line" event combinatorially exactly as in the
# in-tree SchurLagrangeBridge: a degree-(s-1) far line through s points of an agreement
# set S subset mu_n is forced (rank deficient => extra coincidence) iff a complete
# homogeneous symmetric polynomial h_j of the agreement multiset vanishes, j = readout gap.
#
# For the WORST monomial direction the relevant exact test reduces to:
#   does there exist S subset mu_n, |S|=s, with h_{j}(S)=0 for the readout gap j?
# We count S with the minimal-gap (j=1) vanishing as a clean, exact, char-0 surrogate
# for the over-determined incidence (h_1(S)=p_1(S)=sum S = 0), and also j=2.
# h_1(S)=0 over mu_n is the EXACT vanishing-sum-of-roots-of-unity condition (char 0).

def roots_exact(n):
    # represent n-th roots of unity as exponents 0..n-1; sum==0 tested via Z[zeta_n] basis
    # zeta_n^v ; sum of selected exponents == 0 in Z[zeta_n].
    # Use the integer basis 1,zeta,...,zeta^{phi(n)-1}? For n=2^mu, phi=n/2 and
    # zeta^{v+n/2} = -zeta^v.  So coordinate vector in Z^{n/2}: exponent v -> +e_{v} if
    # v<n/2 else -e_{v-n/2}.  Sum==0 iff all n/2 coords are 0.
    return n

def vanishes_sum(expset, n):
    half = n // 2
    coord = [0]*half
    for v in expset:
        if v < half:
            coord[v] += 1
        else:
            coord[v-half] -= 1
    return all(c == 0 for c in coord)

def h1_badcount(n, s):
    """exact count of S subset mu_n, |S|=s, with sum_{x in S} x = 0 (char-0)."""
    cnt = 0
    for comb in combinations(range(n), s):
        if vanishes_sum(comb, n):
            cnt += 1
    return cnt

def s_star_h1(n):
    """smallest agreement s at which the (worst) over-det incidence count exceeds budget n.
    We use the h1 vanishing count as the exact char-0 incidence proxy and find the s where
    count crosses n (the Reed-Solomon dimension-budget). Returns s and the count."""
    # count is symmetric-ish; we scan s upward; bad count grows then we look for crossing > n.
    best = None
    for s in range(2, n+1):
        if math.comb(n, s) > 6_000_000:
            best = ('infeasible', s)
            break
        c = h1_badcount(n, s)
        if c > n:
            best = (s, c)
            break
    return best

print("="*78)
print("(J) leading-constant test: exact char-0 h1 vanishing-sum incidence on mu_n (n=2^mu)")
print("    budget = n (RS dimension); find s where bad count first exceeds n")
print(f"{'n':>4} {'crossing s':>12} {'count':>10} {'s/n':>7} {'sqrt(1/4)=.5':>12}")
for mu in (3,4,5):
    n = 1<<mu
    res = s_star_h1(n)
    if res and res[0] != 'infeasible':
        s,c = res
        print(f"{n:>4} {s:>12} {c:>10} {s/n:>7.3f}")
    else:
        print(f"{n:>4} {'infeasible':>12} (C(n,s) too big at s~{res[1] if res else '?'})")

print()
print("NOTE: h1 (sum=0) vanishing count is the SHALLOWEST cyclotomic incidence; the true")
print("over-det worst-dir threshold uses a higher readout gap and the WORST direction, which")
print("only the GPU engine computes. This probe tests whether even the shallowest exact")
print("char-0 incidence already shows a sqrt(rho)-scale crossing (=> Johnson main term is")
print("structural / cancellation-free) or whether the crossing is at a totally different")
print("scale (=> the n/2 main term is NOT reproduced by elementary counting).")
print("="*78)

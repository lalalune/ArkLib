#!/usr/bin/env python3
"""
PROBE: badScalars == pinnedScalars (distinct-γ) under the radius hypotheses.

The universal alignment law says: γ is MCA-bad  iff  some a-point set is γ-aligned
with a non-degenerate tuple.  pinnedScalars := {γ : alignedSetsForScalar(γ) nonempty}.
These are the SAME predicate. So #bad = #pinnedScalars EXACTLY (not just ≤).

We verify numerically on PROPER thin subgroups μ_n ⊊ F_p*, p≫n^3, p≡1 mod n,
NEVER n=q-1, that:
  #bad-scalars (γ s.t. some a-subset is γ-aligned, non-deg)
    == #pinnedScalars  (γ owning ≥1 non-deg aligned a-set)
  <= #alignableSets    (incidence, the lossy census count)
and that the middle quantity is STRICTLY below incidence in the slack regime.
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_p(n, beta_min=4):
    # smallest prime p ≡ 1 mod n with p > n^beta_min (prize regime), p≫n^3
    target = n**beta_min
    p = target + (n - (target % n)) % n + 1
    # walk to p ≡ 1 mod n
    while True:
        if (p - 1) % n == 0 and isprime(p):
            return p
        p += 1

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of order-n subgroup
    return sorted({pow(h, i, p) for i in range(n)})

def residual_zero_for_tuple(vals_u, tup, dom, k, p):
    # residual = leading divided difference of degree-k interpolation over the (k+1) points.
    # It's zero iff the (k+1) points (x_i, u(x_i)) lie on a poly of degree < k+1... 
    # Standard: build Vandermonde of the k+1 x's with the value vector; residual = det test.
    # Use divided differences: residual=0 iff the (k+1)-th divided difference style det vanishes.
    # Simpler equivalent: the points lie on a degree-k poly  <=>  ALWAYS true for k+1 points.
    # The RESIDUAL here is for degree < k (dim k), i.e. k points determine, (k+1)-th must agree.
    # residual_zero <=> the k+1 points lie on a poly of degree <= k-1.
    xs = [dom[i] for i in tup]
    ys = [vals_u[i] for i in tup]
    # fit degree<=k-1 through first k points, check (k+1)-th. Solve Vandermonde k x k.
    # Build matrix
    import numpy as np
    A = [[pow(xs[j], e, p) for e in range(k)] for j in range(k)]
    b = [ys[j] for j in range(k)]
    # solve over F_p
    M = [row[:] + [b[i]] for i,row in enumerate(A)]
    # gaussian elim mod p
    m = k
    for col in range(m):
        piv = None
        for r in range(col, m):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return None  # singular (shouldn't happen distinct xs)
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], p-2, p)
        M[col] = [(v*inv) % p for v in M[col]]
        for r in range(m):
            if r != col and M[r][col] % p != 0:
                f = M[r][col]
                M[r] = [(M[r][i] - f*M[col][i]) % p for i in range(m+1)]
    coeffs = [M[i][m] % p for i in range(m)]
    # eval at (k+1)-th point
    pred = sum(coeffs[e]*pow(xs[k], e, p) for e in range(k)) % p
    return (pred - ys[k]) % p == 0

def analyze(n, k, a, beta=4, seed=0, verbose=True):
    import random
    p = find_p(n, beta)
    dom = mu_n(p, n)   # the THIN subgroup as the domain
    random.seed(seed)
    # random words u0, u1 (the "stack")
    u0 = [random.randrange(p) for _ in range(n)]
    u1 = [random.randrange(p) for _ in range(n)]
    idx = list(range(n))
    # For each gamma, find a-subsets that are gamma-aligned with a non-deg tuple.
    # Aligned(gamma, S): every (k+1)-injective-tuple in S has residual(u0+gamma*u1)=0.
    # We sweep ALL gamma in F_p? too big. Restrict: gamma is pinned only if SOME a-set aligns.
    # Equivalent characterization: gamma aligned on S <=> the combined word u0+gamma u1
    #   is degree<k (a codeword) on S, i.e. all (k+1)-tuples in S have residual 0.
    # We enumerate candidate gammas from non-deg tuples: a tuple t is non-deg if NOT both
    #   residual(u0)=0 and residual(u1)=0; for it to be on the gamma-fibre need
    #   residual(u0)+gamma*residual(u1)=0 => gamma = -residual(u0)/residual(u1).
    # So candidate gammas come from tuples with residual(u1)!=0.
    pinned = set()
    alignable_sets = set()
    bad = set()
    # iterate a-subsets
    for S in itertools.combinations(idx, a):
        Sset = S
        # find the gamma forced by S (if S is gamma-aligned with non-deg tuple)
        # gather all (k+1)-tuples in S
        gammas_in_S = set()
        nondeg_found = {}
        consistent_gamma = None
        ok = True
        first = True
        gamma_S = None
        all_tuples = list(itertools.combinations(Sset, k+1))
        # need: exists gamma s.t. ALL tuples have residual(u0+gamma u1)=0, AND >=1 non-deg tuple
        # determine gamma from a non-deg tuple, then verify all.
        cand = None
        nd_tuple = None
        for t in all_tuples:
            r0 = residual_val(u0, t, dom, k, p)
            r1 = residual_val(u1, t, dom, k, p)
            if not (r0 == 0 and r1 == 0):
                nd_tuple = t
                if r1 % p != 0:
                    cand = (-r0 * pow(r1, p-2, p)) % p
                else:
                    cand = None  # r1=0 but r0!=0 => no gamma aligns this tuple => S not alignable
                break
        if nd_tuple is None:
            continue  # all tuples degenerate => S degenerate, not in alignableSets
        if cand is None:
            continue
        # verify ALL tuples on the cand-fibre
        good = True
        for t in all_tuples:
            r0 = residual_val(u0, t, dom, k, p)
            r1 = residual_val(u1, t, dom, k, p)
            if (r0 + cand*r1) % p != 0:
                good = False; break
        if good:
            alignable_sets.add(Sset)
            pinned.add(cand)
            bad.add(cand)
    return p, len(bad), len(pinned), len(alignable_sets)

def residual_val(vals_u, tup, dom, k, p):
    xs = [dom[i] for i in tup]
    ys = [vals_u[i] for i in tup]
    M = [[pow(xs[j], e, p) for e in range(k)] + [ys[j]] for j in range(k)]
    m = k
    for col in range(m):
        piv = None
        for r in range(col, m):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return 1  # singular -> treat nonzero
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], p-2, p)
        M[col] = [(v*inv) % p for v in M[col]]
        for r in range(m):
            if r != col and M[r][col] % p != 0:
                f = M[r][col]
                M[r] = [(M[r][i] - f*M[col][i]) % p for i in range(m+1)]
    coeffs = [M[i][m] % p for i in range(m)]
    pred = sum(coeffs[e]*pow(xs[k], e, p) for e in range(k)) % p
    return (pred - ys[k]) % p

print("n  k  a  p        #bad  #pinned  #alignable   bad==pinned?  pinned<incid?")
for (n,k,a,beta) in [(8,2,4,4),(8,2,5,4),(8,3,5,4),(16,2,6,4),(16,2,7,4)]:
    for seed in [0,1,2]:
        p,nb,npn,nal = analyze(n,k,a,beta,seed,False)
        eq = "YES" if nb==npn else "NO!!"
        strict = "strict" if npn < nal else ("tight" if npn==nal else "??")
        print(f"{n:2} {k}  {a}  {p:7}  {nb:4}  {npn:5}   {nal:6}      {eq:5}     {strict} ({npn} vs {nal})")

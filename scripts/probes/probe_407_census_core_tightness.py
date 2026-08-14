#!/usr/bin/env python3
"""
CENSUS<->CORE TIGHTNESS — is the universal census bound  #bad <= #alignableSets  TIGHT,
or strictly LOSSY?  (#407 brief: "the count/census face whose equivalence to CORE is asserted
but NEVER proven — proving that equivalence is itself a real brick.")

In-tree (UniversalAlignmentLaw.lean):
   #{bad gamma} <= #alignableSets(dom,k,a,u0,u1)
where an a-set S is "alignable" if EXISTS gamma with the line u0+gamma*u1 aligned on S (residual=0)
AND S carries a non-degenerate (k+1)-tuple.  This is the count-lane upper bound that feeds delta*.

Equivalence-to-CORE means: bounding #alignableSets is NOT lossy vs the true #bad, i.e. the census
count actually CAPTURES the worst-case incidence (= the CORE sup-norm object via badScalars).
If instead #alignableSets >> #bad with a GROWING gap, the census lane is a strictly weaker handle
and "census == CORE" is FALSE (census overshoots; proving it does NOT prove CORE tightly).

This probe computes BOTH exactly on small thin subgroups (proper mu_n, large prime p>>n^3):
   true #bad(u0,u1) = #{gamma : maxagree(u0+gamma*u1, RS[k]) >= a}          (the CORE/incidence side)
   #alignableSets(u0,u1) = #{a-subsets S of mu_n : EXISTS gamma aligning u0+gamma*u1 on S,
                              S carries a nondegenerate (k+1)-tuple}          (the census side)
at the BINDING radius (a = n - r_bind) and report the ratio #alignableSets / #bad and whether
it is p-independent.  Tight (ratio ~1, bounded) => census==CORE plausible. Growing ratio => LOSSY.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import get_W

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            return p
        p += n

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def rank_mod(rows, p):
    return len(_rref([r[:] for r in rows], p)) - sum(
        1 for r in _rref([r[:] for r in rows], p) if all(x % p == 0 for x in r))

def vander_rank(S, R, k, p):
    """rank of the k-col Vandermonde restricted to rows R."""
    V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
    rr = _rref([row[:] for row in V], p)
    return sum(1 for row in rr if any(x % p for x in row))

def true_bad_and_align(S, p, k, a, u0, u1):
    """Exact: returns (#bad gamma, #alignable a-sets).
    For each a-subset R: aligned gammas = {gamma : u0|_R + gamma u1|_R in col(V_R)}.
      via left null P of V_R:  P u0 + gamma P u1 = 0.
      heavy (all gamma) iff P u0=0 and P u1=0; else <=1 gamma.
    nondegenerate (k+1)-tuple in R exists iff R contains k+1 points with a Vandermonde
      (k+1)x(k+1) ... but RS uses k-dim; nondegeneracy here = R has >= k+1 points NOT all
      in a (k-1)-flat, i.e. vander_rank(R, k) == k (generic) AND |R|>=k+1. For thin mu_n with
      distinct nonzero points any k+1 distinct points are nondegenerate => condition is |R|>=k+1.
    #bad = |union over R of aligned gammas (heavy => all p)|.
    #alignable = #{R : aligned set nonempty AND R has a nondeg (k+1)-tuple AND not (residual u0=0 & u1=0)}.
    """
    n = len(S); size = a
    if size <= k: return p, 0  # degenerate
    bad = set(); align = 0; heavy_seen = False
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P:
            continue
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        # nondegenerate (k+1)-tuple: |R|>=k+1 (true here since a>k) and NOT both residuals zero
        nd_exists = (size >= k + 1) and not (all(x % p == 0 for x in pa) and all(x % p == 0 for x in pb))
        if not any(pb):
            if not any(pa):
                heavy_seen = True
                if nd_exists: align += 1   # heavy & nondeg => alignable for all gamma
                continue
            else:
                continue  # no gamma aligns
        # single gamma
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            bad.add(g)
            if nd_exists: align += 1
    nbad = p if heavy_seen else len(bad)
    return nbad, align

def mono(S, p, e): return [pow(int(x), e, p) for x in S]

if __name__ == '__main__':
    # n=16 k=4 binding radius r=10 => a=n-r=6 (the BAD rung where mono incidence 89>budget).
    # also r=9 => a=7 (the GOOD rung that sets delta*=9/16).
    # Use the binding monomial direction u0=x^10,u1=x^4 (the c.94/c.125 binder).
    n, k = 16, 4
    print(f"== CENSUS<->CORE TIGHTNESS  n={n} k={k} rho={k/n} ==")
    print("binding monomial direction u0=x^10, u1=x^4 (the in-tree delta* binder).")
    print("ratio = #alignableSets / #bad.  ~1 & p-indep => census==CORE tight; growing => LOSSY.\n")
    for r in (9, 10):
        a = n - r
        print(f"-- radius r={r}  (a=n-r={a}) --")
        for plo in (200003, 500003, 1000003):
            p = find_prime_cong1(n, plo)
            S = list(get_W(n, p).S)
            u0 = mono(S, p, 10); u1 = mono(S, p, 4)
            nbad, nalign = true_bad_and_align(S, p, k, a, u0, u1)
            ratio = (nalign / nbad) if nbad else float('inf')
            print(f"   p={p}: #bad={nbad:>4}  #alignableSets={nalign:>5}  ratio={ratio:.3f}")
        print()

#!/usr/bin/env python3
"""
probe_fisher_twolevel_listcap.py  (#444 CORE-side, NON-census, polynomial-method)

LANE: the past-Johnson Fisher/polynomial-method list cap (FisherPastJohnsonCap.lean,
`card_le_choose_div_choose_of_pairwise_inter`: F.card * C(t,a+1) <= C(n,a+1)).

The deployed bound is the FLAT single-parameter cap using only the max pairwise
intersection a. QUESTION (probe-first, before formalizing anything): does the
realized agreement-set family of an RS code over a THIN 2-power subgroup mu_n have
pairwise-intersection STRUCTURE the flat cap ignores, such that a 2nd-level
correction (subtract the over-counted (a+1)-subsets that lie in >=2 members) gives
a strictly smaller, still-rigorous cap?

The Bonferroni/inclusion-exclusion sharpening of the disjoint-slice count is:
  sum_S C(|S|,k)  =  |union of slices|  +  (over-counts)
The flat bound drops the over-counts (assumes slices DISJOINT, true only when all
pairwise inter < k). When some pairwise inter == a == k-1 the slices ARE disjoint
(C(a,k)=0 since k=a+1>a). So at k=a+1 the slices are ALWAYS disjoint -> NO
over-count to reclaim. CONCLUSION-IN-ADVANCE: the flat k=a+1 bound is already
inclusion-exclusion-exact at its own level; a 2nd-level correction is VACUOUS at
k=a+1. The only lever is using a LARGER k where slices CAN overlap and the
over-count is reclaimable -- but C(n,k)/C(t,k) is increasing in k, so a larger-k
flat bound is WORSE, and the over-count reclaim would have to beat that gap.

This probe MEASURES, on real prize-regime RS agreement families, whether ANY level
k in [a+1, t] (flat OR Bonferroni-corrected) beats the deployed k=a+1 flat cap.
If none does, that is an honest WALL result (the polynomial-method level is locked
at a+1) -> DISPROOF_LOG. If some k wins, that is a real sharpening -> formalize.

PROPER thin mu_n subgroups, p >> n^3, p == 1 mod n. NEVER n=q-1.
"""
import itertools, math
from math import comb

def find_prime(min_p, n):
    # smallest prime p > min_p with p == 1 mod n
    p = ((min_p // n) + 1) * n + 1
    while True:
        if is_prime(p):
            return p
        p += n

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def subgroup_mu_n(p, n):
    # the order-n subgroup of F_p^* (p == 1 mod n)
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x*h) % p
    assert len(set(S)) == n
    return S

def primitive_root(p):
    if p == 2: return 1
    factors = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in factors):
            return g
    raise RuntimeError("no prim root")

def factorize(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def rs_codewords_low_degree(dom, p, k):
    """All RS codewords (deg < k) as tuples of values on dom. |F|^k of them -> only
    enumerate for small p^k. We instead sample codewords as eval of random low-deg
    polys; for the agreement-family experiment we build the list around a center."""
    raise NotImplementedError

def agreement_family_around_center(dom, p, k, w, t):
    """Return the family of agreement-sets {i : c(dom_i)=w_i} for every deg<k codeword
    c whose agreement with center word w is >= t. dom: list of field elts (the thin mu_n).
    Enumerate all deg<k polynomials over F_p (feasible only for small p^k)."""
    n = len(dom)
    fam = []
    # enumerate poly coeffs (a_0..a_{k-1}) in F_p^k
    for coeffs in itertools.product(range(p), repeat=k):
        agree = []
        for i, x in enumerate(dom):
            val = 0
            xp = 1
            for c in coeffs:
                val = (val + c*xp) % p
                xp = (xp*x) % p
            if val == w[i]:
                agree.append(i)
        if len(agree) >= t:
            fam.append(frozenset(agree))
    # dedup (distinct codewords can share an agreement set only if equal on >k-1 pts => equal)
    return list(set(fam))

def flat_cap(n, t, a):
    k = a + 1
    if k > t: return math.inf
    denom = comb(t, k)
    if denom == 0: return math.inf
    return comb(n, k) / denom

def best_level_flat_cap(n, t, a):
    """min over k in [a+1, t] of C(n,k)/C(t,k) (all rigorous flat bounds)."""
    best = math.inf; bk = None
    for k in range(a+1, t+1):
        d = comb(t, k)
        if d == 0: continue
        v = comb(n, k)/d
        if v < best:
            best, bk = v, k
    return best, bk

def main():
    print("== Fisher two-level / multi-level list-cap probe (CORE-side, prize-regime) ==")
    print("Measuring: realized list size vs flat k=a+1 cap vs best-level flat cap.\n")
    # small k so p^k enumeration is feasible; thin mu_n, p>>n^3
    configs = [
        (4, 2),   # n=4, k=2  (linear codewords)
        (6, 2),
        (8, 2),
        (4, 3),
        (6, 3),
    ]
    import random
    random.seed(1)
    for (n, k) in configs:
        min_p = max(n**3, 50)
        p = find_prime(min_p, n)
        if p**k > 4_000_000:
            # cap enumeration cost
            print(f"n={n} k={k} p={p}: SKIP (p^k={p**k} too large to enumerate)")
            continue
        dom = subgroup_mu_n(p, n)
        a = k - 1  # RS pairwise agreement cap (min distance d=n-(k-1))
        # pick a few random center words; report worst (largest realized list)
        worst = None
        for _ in range(6):
            w = [random.randrange(p) for _ in range(n)]
            # sweep t from just-past-Johnson down toward small
            for t in range(k, n+1):
                fam = agreement_family_around_center(dom, p, k, w, t)
                L = len(fam)
                if L == 0:
                    continue
                # measured max pairwise intersection
                amax = 0
                for i in range(len(fam)):
                    for j in range(i+1, len(fam)):
                        amax = max(amax, len(fam[i] & fam[j]))
                fc = flat_cap(n, t, a)
                bc, bk = best_level_flat_cap(n, t, a)
                rec = (t, L, amax, a, fc, bc, bk)
                if worst is None or L > worst[1]:
                    worst = rec
        if worst:
            t, L, amax, a, fc, bc, bk = worst
            johnson_vac = (t*t - a*n) <= 0
            print(f"n={n} k={k} p={p}: WORST t={t}  realized L={L}  measured amax={amax} (a={a})")
            print(f"   flat k=a+1 cap = {fc:.3f}   best-level flat cap = {bc:.3f} (at k={bk})")
            print(f"   Johnson denom t^2-a*n = {t*t-a*n} {'(VACUOUS, Fisher regime)' if johnson_vac else ''}")
            print(f"   best-level beats k=a+1? {'YES' if bc < fc - 1e-9 else 'NO (k=a+1 optimal)'}")
        print()

if __name__ == "__main__":
    main()

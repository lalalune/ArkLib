#!/usr/bin/env python3
"""
UNDER-DET / AGREEMENT-SHARING lane (#444). THE QUESTION (brief): does the agreement-SHARING
contribution to the census (one a-set aligned for MULTIPLE scalars gamma = pairJointAgreesOn)
sustain a window-interior gap, or COLLAPSE to Johnson like the over-det/combinatorial face?

STRUCTURAL CLAIM to test:
  An a-set S aligned for TWO distinct scalars g1 != g2 forces BOTH pencils u0+g1 u1 and u0+g2 u1
  to be deg-<k-explainable on S. Subtracting: (g1-g2) u1 is deg-<k on S => u1 is deg-<k on S,
  hence u0 too => pairJointAgreesOn C S u0 u1 (joint agreement). Joint agreement means S is
  contained in the COMMON agreement set of two FIXED deg-<k codewords v0,v1, which is the
  intersection of two codeword-agreement sets => |S| <= (agreement radius of a deg-<k codeword
  with a generic word) = the Johnson/list-decoding cap, NOT n/2.

So: multi-gamma-aligned (shared) sets should be SMALL (Johnson-capped, ~k-controlled), while
single-gamma-aligned sets reach the deep band a0 ~ rm = n/2-ish. If true, the SHARING is
Johnson-side => the census double-counting Sum_g C(|A_g|,a) over-counts only at SHALLOW bands,
and at the DEEP binding band a >= a0 every aligned set has multiplicity 1 (no sharing) =>
census = distinct-gamma count there => the sharing contributes NOTHING at the binding band =>
collapses to the over-det/Johnson picture. EITHER outcome is a real result.

MEASURE, exact mod p, PROPER mu_n (n=2^a), p >> n^3, multi-prime, NEVER n=q-1:
  For worst-case structured stacks (u0,u1) = adjacent high-freq char lines near n/2:
  for each a-set S of size a, count mult(S) = #{distinct gamma : S is gamma-aligned (k+1-tuples
  explained)}. Report, per band a:
    - max set-size reachable with mult >= 2 (the SHARED cap)
    - max set-size reachable with mult == 1 (the single-gamma reach, ~ deep band)
  The structural prediction: shared-cap << single-cap, and shared-cap is k-controlled (Johnson),
  while single-cap rides the n/2 cliff.
"""
import sys, itertools
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime(n, mult_lo):
    p = mult_lo*n
    p += (1 - p) % n
    if p < 3: p = n+1
    while True:
        if p>2 and p%n==1 and all(p%d for d in range(2,int(p**0.5)+1)):
            return p
        p += n

def find_g(p, n):
    for h in range(2, 20000):
        x = pow(h, (p-1)//n, p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in prime_factors(n)):
            return x
    raise ValueError("no generator")

def divided_diff(vals, T, xs, p):
    """order-k divided difference (residual functional) of word `vals` on tuple T (len k+1)."""
    acc = 0
    for i in T:
        den = 1
        for j in T:
            if i != j:
                den = den*((xs[i]-xs[j]) % p) % p
        acc = (acc + vals[i]*pow(den, -1, p)) % p
    return acc

def analyze(n, beta_target, k, bands):
    # prime p ~ n^beta, p = 1 mod n, p >> n^3
    p = find_prime(n, max(n**(beta_target-1), n**3))
    g = find_g(p, n)
    xs = [pow(g, i, p) for i in range(n)]   # the thin subgroup mu_n
    # worst-case structured stack: adjacent high-freq char "lines" near n/2
    # u0 = x^{n/2}, u1 = x^{n/2 - 1}  (the antipodal-adjacent binder family)
    a_exp = n//2
    b_exp = n//2 - 1
    u0 = [pow(x, a_exp, p) for x in xs]
    u1 = [pow(x, b_exp, p) for x in xs]
    out = {}
    # precompute residuals over all (k+1)-tuples
    Tlist = list(itertools.combinations(range(n), k+1))
    e0 = {}; e1 = {}
    for T in Tlist:
        e0[T] = divided_diff(u0, T, xs, p)
        e1[T] = divided_diff(u1, T, xs, p)
    # a set S is gamma-aligned iff for ALL (k+1)-subtuples T of S: e0[T] + gamma*e1[T] = 0.
    # The set of valid gamma for a fixed S: intersection over T in C(S,k+1) of {gamma : e0+gamma e1=0}.
    #   if e1[T]!=0: forces gamma = -e0[T]/e1[T] (single value)
    #   if e1[T]==0 and e0[T]==0: no constraint (any gamma)
    #   if e1[T]==0 and e0[T]!=0: NO gamma (S not aligned at all)
    # mult(S) = #valid gamma (could be "all p" if every T is doubly-zero -> joint-deg<k).
    def valid_gammas(S):
        forced = None
        all_double_zero = True
        for T in itertools.combinations(sorted(S), k+1):
            a_, b_ = e0[T], e1[T]
            if b_ == 0:
                if a_ != 0:
                    return ("none", 0)
                # double zero: no constraint
            else:
                all_double_zero = False
                gv = (-a_ * pow(b_, -1, p)) % p
                if forced is None:
                    forced = gv
                elif forced != gv:
                    return ("none", 0)
        if all_double_zero:
            return ("all", p)   # jointly deg-<k on S: aligned for EVERY gamma (pairJointAgreesOn at full)
        return ("one", 1) if forced is not None else ("all", p)
    for a in bands:
        max_shared = 0   # largest |S|=a with mult>=2 (i.e. "all" => >=2 since p>2)
        max_single = 0
        n_all = 0
        for S in itertools.combinations(range(n), a):
            tag, mult = valid_gammas(set(S))
            if tag == "all":
                n_all += 1
                max_shared = a
            elif tag == "one":
                max_single = a
        out[a] = dict(p=p, max_shared=max_shared, max_single=max_single, n_jointly_degk=n_all)
    return p, out

if __name__ == "__main__":
    # keep enumeration feasible: small n, focus on band structure around the cliff
    for n in [8, 12, 16]:
        k = 2  # rate rho = k/n; r-2 m+1 = k => modest k for enumeration
        # bands from shallow up toward the n/2 cliff; cap to keep C(n,a) feasible
        maxband = min(n, 9)
        bands = list(range(k+1, maxband+1))
        print(f"\n=== n={n} k={k} (deg<k => deg<=1 codewords) ===")
        for beta in [3.5]:
            p, out = analyze(n, beta, k, bands)
            print(f"  p={p} (beta~{beta}), worst line (x^{n//2}, x^{n//2-1})")
            print(f"  {'a':>3} {'maxSHARED(mult>=2)':>18} {'maxSINGLE(mult=1)':>18} {'#jointly-deg<k':>14}")
            for a in bands:
                d = out[a]
                print(f"  {a:>3} {d['max_shared']:>18} {d['max_single']:>18} {d['n_jointly_degk']:>14}")

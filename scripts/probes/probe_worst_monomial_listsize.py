#!/usr/bin/env python3
"""
PROBE: list size at the worst monomial word x^{n/2} over the THIN 2-power subgroup mu_n.

Claim (named-open in UncertaintyTwoPowerExtremal): the single-line beyond-Johnson agreement
excess (s* = n/2 + 2^floor(log2(k-1)), exceeding Johnson sqrt(kn)=n/2 by a constant) does NOT
lift to a large LIST. At the binding/Johnson radius the number of DISTINCT deg-<k codewords
agreeing with the worst monomial word on >= s points is O(1) (= 2 at the n/2-coset radius:
the +1/-1 coset interpolants), NOT exploding.

Setup (prize-regime faithful):
- F_p, p >> n (so char-0 faithful), n = 2^a, mu_n = <g^{(p-1)/n}> PROPER subgroup (NEVER n=q-1).
- worst word w(x) = x^{n/2} for x in mu_n. Since x has order n=2^a, x^{n/2} = +-1 (2-valued),
  so w takes value -1 on the "-1 coset" (n/2 pts) and +1 on the "+1 coset" (n/2 pts).
- LIST(s) = number of distinct polynomials c of degree < k such that
      #{x in mu_n : c(x) == w(x)} >= s.
  We enumerate this EXACTLY by: for every subset A of mu_n with |A| >= s, the unique deg<|A|
  interpolant through (x, w(x)) for x in A; keep those of degree < k. Distinct polys counted once.
  (This is exact list-decoding of the worst word at radius n-s.)

We report LIST(s) at s = n/2 (binding) and a sweep s = n/2 .. n, across n,k,primes.
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_prime(n, lower):
    # need p prime, p ≡ 1 mod n, p > lower
    p = lower - (lower % n) + 1
    if p <= lower: p += n
    while not isprime(p):
        p += n
    return p

def subgroup_mu(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of mu_n
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur)
        cur = (cur*h) % p
    assert len(set(elts)) == n, "mu_n not size n"
    return elts, h

def lagrange_coeffs(points, p):
    # points: list of (x,y) in F_p, distinct x. Returns coeff list (len=len(points)) of interp poly.
    k = len(points)
    coeffs = [0]*k
    for i,(xi,yi) in enumerate(points):
        # basis poly L_i(X) = prod_{j!=i} (X-xj)/(xi-xj)
        num = [1]  # poly coeffs low->high
        den = 1
        for j,(xj,_) in enumerate(points):
            if j==i: continue
            # multiply num by (X - xj)
            new = [0]*(len(num)+1)
            for d,c in enumerate(num):
                new[d]   = (new[d]   - c*xj) % p
                new[d+1] = (new[d+1] + c) % p
            num = new
            den = (den * (xi - xj)) % p
        invden = pow(den % p, p-2, p)
        scale = (yi * invden) % p
        for d in range(len(num)):
            coeffs[d] = (coeffs[d] + num[d]*scale) % p
    # trim
    while len(coeffs)>1 and coeffs[-1]==0:
        coeffs.pop()
    return tuple(coeffs)

def poly_deg(c):
    d=len(c)-1
    while d>0 and c[d]==0: d-=1
    return d

def worst_word(mu, p, half_pow):
    # w(x) = x^{half_pow} = x^{n/2} in F_p
    return {x: pow(x, half_pow, p) for x in mu}

def list_at(mu, w, p, k, s):
    """EXACT list: distinct deg<k interpolants agreeing with w on >= s points of mu."""
    n = len(mu)
    found = set()
    # enumerate minimal interpolant supports: any deg<k poly agreeing on >=s pts is determined
    # by any k of its agreement points; so enumerate k-subsets, interpolate, then verify agreement>=s.
    # (Brute but exact for small n,k.)
    for combo in itertools.combinations(mu, k):
        pts = [(x, w[x]) for x in combo]
        # need distinct x (always true), interpolate deg<k
        c = lagrange_coeffs(pts, p)
        if poly_deg(c) >= k:
            continue
        # count agreement with w over all mu
        agree = sum(1 for x in mu if poly_eval(c,x,p)==w[x])
        if agree >= s:
            found.add(c)
    return found

def poly_eval(c,x,p):
    r=0
    for coef in reversed(c):
        r=(r*x+coef)%p
    return r

def main():
    print("# worst-monomial list-size probe — thin mu_n, char-0 faithful (p>>n)")
    print("# LIST(s) = #distinct deg<k polys agreeing with w(x)=x^(n/2) on >= s points of mu_n\n")
    cases = [
        (8, 2), (8, 3),
        (16, 2), (16, 4),
        (32, 2), (32, 4),
    ]
    for (n,k) in cases:
        half = n//2
        # two primes per (n) for char-0 faithfulness; p >> n^3
        primes = []
        lo = n*n*n*50
        pp = find_prime(n, lo)
        primes.append(pp)
        primes.append(find_prime(n, pp+1))
        for p in primes:
            mu, h = subgroup_mu(p, n)
            w = worst_word(mu, p, half)
            # sweep s from n/2 (Johnson binding) up to n
            johnson = half  # sqrt(k n) >= n/2 only at k>=n/... actually Johnson = sqrt(kn); report n/2 binding
            srow = []
            for s in range(half, n+1):
                if n>=32 and k>=4:
                    # brute C(n,k) too big for n=32,k=4 (C(32,4)=35960 ok) — keep
                    pass
                L = list_at(mu, w, p, k, s)
                srow.append((s, len(L)))
            # print compact: s=n/2 value + where it drops to <=2 + max over sweep
            at_half = srow[0][1]
            maxL = max(v for _,v in srow)
            # find list at s slightly above n/2
            print(f"n={n:3d} k={k} p={p:>10d}  LIST(n/2={half}) = {at_half:4d}   maxL_over_sweep={maxL:4d}   sweep[s,L]={srow}")
        print()

if __name__=='__main__':
    main()

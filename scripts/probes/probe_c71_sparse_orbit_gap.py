#!/usr/bin/env python3
"""
#444 -- the SHARP question inside Conjecture 7.1 (2026/861), after the dominance probe walled on
compute: does "<=3-sparse worst case" actually buy the action-orbit O(1)/|F| closure?

The in-tree ActionOrbitGeneralF PIN: per-line gamma-orbit closure of the bad set holds <=> the
direction f is a dilation eigenvector <=> f is a single MONOMIAL (eigen_forces_monomial, when
orderOf(mu) > deg f). So orbit-closure is a 1-SPARSE (monomial) property, NOT a 3-sparse one.

Conjecture 7.1 says the worst-case witness is <=3-sparse. If TRUE, that still leaves a 2- or
3-term direction as the worst case -- which by the PIN is NOT a dilation eigenvector, so its bad
set is NOT a union of gamma-orbits and gets NO O(1)/|F| orbit compression. So either:
  (A) Conj 7.1's "sparse" worst case is specifically 1-sparse (monomial), in which case the
      monomial-strata orbit bound DOES close it (great, and the in-tree pin is exactly the tool); OR
  (B) the worst case is genuinely 2- or 3-sparse (multi-term), in which case orbit-closure FAILS
      on the worst case and 2026/861's reduction to "sparse" still needs a NON-orbit incidence
      argument on the 2-3 term strata = a residual that the in-tree machinery does NOT yet supply.

THIS PROBE decides A vs B finitely: among the <=3-sparse directions on thin mu_n, is the MAX bad-set
(adversary) strength achieved by a 1-sparse (monomial) direction, or strictly by a 2-/3-term one?
  s1max = max bad-set strength over 1-sparse (monomial) directions
  s23max = max over 2- and 3-sparse directions
If s1max >= s23max  => worst sparse case is monomial => orbit pin closes it (route A).
If s23max > s1max   => worst sparse case is multi-term => orbit pin does NOT cover the worst case
                       => residual incidence brick needed (route B); names the exact open gap.

Affine pencil model {g0 + alpha f}, g0 a degree-(k+1) monomial NOT in RS. Strength = |BAD_thr| at
the Johnson agreement threshold. EXACT full alpha sweep over small p>=... ; thin mu_n n=2^a; NEVER
n=q-1; multi-prime incl p>n^3.
"""
import itertools, random
from math import gcd, comb, sqrt, ceil

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out = []; p = (lo | 1)
    while len(out) < cap:
        if (p - 1) % n == 0 and is_prime(p):
            out.append(p)
        p += 2
    return out

def prime_factors(m):
    fs = []; d = 2
    while d*d <= m:
        while m % d == 0:
            fs.append(d); m //= d
        d += 1
    if m > 1: fs.append(m)
    return fs

def root_of_unity(p, n):
    g = 2
    while True:
        w = pow(g, (p-1)//n, p)
        if w != 1 and pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in set(prime_factors(n))):
            return w
        g += 1

def max_agreement_to_RS(v, dom, k, p):
    n = len(dom); idx = list(range(n)); best = 0
    subs = list(itertools.combinations(idx, k))   # exact for n=8,k=2 (C(8,2)=28)
    for S in subs:
        xs = [dom[i] for i in S]; ys = [v[i] for i in S]; agree = 0
        for jj in range(n):
            xq = dom[jj]; num = 0
            for a in range(k):
                term = ys[a]; xa = xs[a]
                for b in range(k):
                    if b == a: continue
                    term = term * ((xq - xs[b]) % p) % p * pow((xa - xs[b]) % p, p-2, p) % p
                num = (num + term) % p
            if num == v[jj]:
                agree += 1
        if agree > best:
            best = agree
            if best == n: break
    return best

def bad_strength(fvals, dom, k, p, thr, g0vals):
    n = len(dom); bad = 0
    for alpha in range(1, p):
        v = [(g0vals[j] + alpha*fvals[j]) % p for j in range(n)]
        if max_agreement_to_RS(v, dom, k, p) >= thr:
            bad += 1
    return bad

def evalf(coeffs, dom, p):
    return [sum(c*pow(x,pos,p) for pos,c in coeffs.items()) % p for x in dom]

def run(n, plist, k):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson-agreement thr={thr}/{n} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        assert len(set(dom)) == n
        g0 = evalf({k+1: 1}, dom, p)
        tag = "p>n^3" if p > n**3 else "p<=n^3"
        # 1-sparse: monomials X^b, b in 1..n-1
        s1 = 0
        for b in range(1, n):
            fv = evalf({b: 1}, dom, p)
            s1 = max(s1, bad_strength(fv, dom, k, p, thr, g0))
        # 2-sparse and 3-sparse (cap supports for budget; unit + mixed coeffs)
        s23 = 0
        for s in (2, 3):
            supports = list(itertools.combinations(range(1, n), s))
            random.seed(11); 
            if len(supports) > 25: supports = random.sample(supports, 25)
            for supp in supports:
                for cp in ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1)):
                    cf = {supp[i]: cp[i] for i in range(s)}
                    fv = evalf(cf, dom, p)
                    if all(x==0 for x in fv): continue
                    s23 = max(s23, bad_strength(fv, dom, k, p, thr, g0))
        verdict = "A (monomial worst => orbit pin closes)" if s1 >= s23 else \
                  "B (multi-term worst => orbit pin MISSES worst case; residual incidence brick needed)"
        print(f"  p={p} ({tag}): s1max(monomial)={s1}  s23max(2-3 term)={s23}  => ROUTE {verdict}")

if __name__ == "__main__":
    for n in [8]:
        k = max(2, n//4)
        small = primes_1_mod_n(n, 2*n, 2)          # p<=n^3 surplus: 17, 41
        large = primes_1_mod_n(n, n**3+1, 1)       # p>n^3 equality regime: 521
        run(n, small + large, k)
    print("\nDONE")

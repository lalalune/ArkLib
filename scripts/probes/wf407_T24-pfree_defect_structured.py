"""
wf407 / T24-pfree, PART 4 : the STRUCTURED-PRIME non-uniformity (the wall location).

Two questions decided here:
(A) Is the defect onset SIZE-monotone (then a p-free bound would transfer for all
    p above a size threshold = a clean p-uniform statement), or is it ARITHMETIC
    (structured: a particular large p can carry a defect that a smaller p does not)?
    If arithmetic, "p-uniform-from-p-free" is FALSE as a clean size statement.
(B) Pin the defect mechanism: D_r(q) > 0  <=>  exists nonzero sparse alpha
    (<= 2r roots-of-unity, NOT vanishing over C) with p | N(alpha).  Show a SINGLE
    large structured prime where the p-free bound is violated while a much SMALLER
    prime is fine.
"""

import itertools, math
from collections import Counter

def prime_factors(n):
    fs = set(); d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d); n //= d
        d += 1
    if n > 1: fs.add(n)
    return fs

def is_prime(p):
    if p < 2: return False
    for d in range(2, int(p**0.5) + 1):
        if p % d == 0: return False
    return True

def primes_eq1_modn(n, lo, hi):
    out = []; p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while p <= hi:
        if is_prime(p): out.append(p)
        p += n
    return out

def roots_mod_p(n, p):
    pf = prime_factors(n)
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1 for q in pf):
            return [pow(cand, i, p) for i in range(n)]
    raise RuntimeError

def E_r_char_p_fast(n, r, p, roots):
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for v, c in dist.items():
            for x in roots:
                nd[(v + x) % p] += c
        dist = nd
    return sum(c * c for c in dist.values())

def char0_zero_pow2(plus, minus, n):
    h = n // 2; coeff = [0] * h
    for a in plus:  coeff[a % h] += (-1 if (a // h) % 2 else 1)
    for b in minus: coeff[b % h] -= (-1 if (b // h) % 2 else 1)
    return all(c == 0 for c in coeff)

def E_r_char0(n, r):
    cnt = 0
    for xs in itertools.product(range(n), repeat=r):
        for ys in itertools.product(range(n), repeat=r):
            if char0_zero_pow2(xs, ys, n): cnt += 1
    return cnt

print("=" * 80)
print("PART 4A: is defect onset SIZE-monotone or ARITHMETIC (structured)?")
print("=" * 80)
print("Scan ALL primes p=1 mod n in a band; record, at fixed r, which have a defect.")
print("If clean-set is a clean upper interval [P0, inf) -> size threshold (p-uniform OK).")
print("If a SMALLER p is clean while a LARGER p has a defect -> ARITHMETIC (no p-uniform).")
print()

for n, r, band in [(8, 3, (8, 2000)), (16, 2, (16, 4000))]:
    Einf = E_r_char0(n, r)
    ps = primes_eq1_modn(n, *band)
    rows = []
    for p in ps:
        roots = roots_mod_p(n, p)
        D = E_r_char_p_fast(n, r, p, roots) - Einf
        rows.append((p, D))
    # find clean primes and the smallest defect prime above some clean prime
    clean = [p for p, D in rows if D == 0]
    defect = [(p, D) for p, D in rows if D > 0]
    print(f"--- n={n}, r={r}, E_inf={Einf}: {len(ps)} primes in {band} ---")
    print(f"    #clean={len(clean)}  #defect={len(defect)}")
    if clean and defect:
        smallest_clean = min(clean)
        # large structured primes ABOVE a clean prime that still carry a defect
        struct = [(p, D) for p, D in defect if p > smallest_clean]
        print(f"    smallest CLEAN prime = {smallest_clean}")
        print(f"    LARGER primes that STILL carry a defect (structured, > {smallest_clean}):")
        for p, D in struct[:12]:
            print(f"        p={p}  (log_n p={math.log(p,n):.2f})  D_{r}={D}  "
                  f"[smaller clean prime {smallest_clean} exists!]")
        if not struct:
            print("        (none -> onset is size-monotone here)")
    print()

print("=" * 80)
print("PART 4B: norm mechanism --- a structured prime divides a sparse-alpha norm")
print("=" * 80)
print("Defect tuple at r: alpha = sum x - sum y, <=2r roots, alpha != 0 over C, p|N(alpha).")
print("Show: the structured defect primes are EXACTLY odd prime factors of {N(alpha)}.")
print()

# Build the set of sparse alphas (as Z[zeta_n] elements via the half-basis) for small r,
# compute their algebraic norm (product of Galois conjugates) and factor it.
import cmath
def alpha_norm_pow2(coeff, n):
    """coeff: vector length n/2 giving alpha = sum coeff_k zeta^k (basis zeta^{n/2}=-1).
       Norm = prod over primitive embeddings sigma of |sigma(alpha)|^2 contributions...
       We compute the integer norm N_{Q(zeta_n)/Q}(alpha) = prod_{t in (Z/n)^*} sigma_t(alpha)."""
    h = n // 2
    units = [t for t in range(1, n) if math.gcd(t, n) == 1]
    prod = 1.0 + 0j
    for t in units:
        s = 0 + 0j
        for k in range(h):
            # zeta_n^{t*k}, reduce via zeta^{h}=-1
            e = (t * k)
            sign = -1 if (e // h) % 2 else 1
            s += coeff[k] * sign * cmath.exp(2j * math.pi * (e % h) / n) * 0  # placeholder
        prod *= s
    return prod

# Simpler & exact: enumerate sparse alphas as multiset of root-exponents, get the
# minimal half-basis integer vector, and compute the resultant-based norm via numpy roots.
import numpy as np
def sparse_alpha_norm(plus, minus, n):
    h = n // 2
    coeff = [0] * h
    for a in plus:  coeff[a % h] += (-1 if (a // h) % 2 else 1)
    for b in minus: coeff[b % h] -= (-1 if (b // h) % 2 else 1)
    if all(c == 0 for c in coeff):
        return 0
    # alpha = f(zeta) with f(X)=sum coeff_k X^k, deg < h ; minpoly of zeta_n (n=2^a) is X^h+1
    # Norm = Res(X^h + 1, f(X)) / lc(X^h+1)^deg... = prod_{f(rho)=0 of minpoly} ... actually
    # N(alpha) = prod_{rho^h=-1} f(rho).  Compute numerically, round to nearest int.
    roots = [cmath.exp(1j * math.pi * (2 * j + 1) / h) for j in range(h)]
    prod = 1.0 + 0j
    for rho in roots:
        val = sum(coeff[k] * rho ** k for k in range(h))
        prod *= val
    return int(round(prod.real))

def factor(m):
    m = abs(m); fs = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs[d] = fs.get(d, 0) + 1; m //= d
        d += 1
    if m > 1: fs[m] = fs.get(m, 0) + 1
    return fs

for n, r in [(8, 3)]:
    print(f"--- n={n}, r={r}: norms of sparse alphas (<= {2*r} roots) and their odd prime factors ---")
    normset = set()
    seen = set()
    for plus in itertools.combinations_with_replacement(range(n), r):
        for minus in itertools.combinations_with_replacement(range(n), r):
            key = (plus, minus)
            N = sparse_alpha_norm(plus, minus, n)
            if N != 0:
                normset.add(abs(N))
    oddfactors = set()
    for N in normset:
        for q, _ in factor(N).items():
            if q % 2 == 1 and q % n == 1:
                oddfactors.add(q)
    print(f"    #distinct nonzero |N(alpha)| = {len(normset)}")
    small_odd = sorted(q for q in oddfactors if q < 2000)
    print(f"    odd primes q=1 mod n dividing some N(alpha), q<2000:")
    print(f"        {small_odd}")
    # cross-check against measured defect primes
    Einf = E_r_char0(n, r)
    measured = []
    for p in primes_eq1_modn(n, 8, 2000):
        roots = roots_mod_p(n, p)
        if E_r_char_p_fast(n, r, p, roots) - Einf > 0:
            measured.append(p)
    print(f"    MEASURED defect primes (D_{r}>0), p<2000: {measured}")
    print(f"    MATCH (norm-factors == measured defects)? "
          f"{set(small_odd) == set(measured)}")

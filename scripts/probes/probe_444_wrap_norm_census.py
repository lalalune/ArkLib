#!/usr/bin/env python3
"""
probe_444_wrap_norm_census.py  (#444, C1-anomaly-wrap-count: the HEIGHT/NORM census)

The decisive structural object. A char-p anomaly tuple is a signed 2r-tuple of mu_n whose
element  S = sum_{i} eps_i zeta^{a_i}  in Z[zeta_n]  is NONZERO but  S = 0 (mod P|p).
S != 0, S in P  =>  p | N(S),  where N(S) = prod over embeddings = |Res(min..)| is an INTEGER.

So the set of primes that can EVER produce an A_r-anomaly is exactly
        BAD(n,r) = { p prime : p | N(S) for some signed 2r-tuple with S != 0 }.
The WRAP THRESHOLD T(n,r) = max BAD(n,r) = largest prime dividing any such N(S).
For p > T(n,r):  A_r = 0 EXACTLY (perfect faithfulness), with NO prime scan needed.

This probe computes, EXACTLY (n = 2^k so zeta^{n/2} = -1; embeddings sigma_t: zeta -> zeta^t, t odd):
  - the distribution of |N(S)| over all signed 2r-tuples with S != 0,
  - max |N(S)|  (compare to naive height bound (2r)^{phi(n)}),
  - the largest PRIME factor appearing across all N(S)  = T(n,r) = the true wrap wall,
  - and how T(n,r) scales:  is it BELOW the prize band n^4..n^5 at prize depth r?

If T(n,r) < n^4 at r ~ log m  =>  the anomaly is structurally ABSENT in the prize regime: A_r=0,
so E_r^{Fp,nonzero} = E_r^{char0,nonzero} <= Wick EXACTLY -> R_r <= 1 reduces to the (proven) char-0
ceiling.  That would be a real handle. If T(n,r) >> n^5  =>  height alone gives no gain.

EXACT integer arithmetic (Python big ints). Probe-only => axiom-clean trivially. Proper mu_n.
"""
import sys, math
from itertools import product
from functools import reduce

def primes_up_to(N):
    sieve = bytearray([1])*(N+1); sieve[0]=sieve[1]=0
    for i in range(2,int(N**0.5)+1):
        if sieve[i]:
            sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
    return [i for i in range(N+1) if sieve[i]]

def largest_prime_factor(m, small_primes):
    m = abs(m)
    if m <= 1: return 1
    lpf = 1
    for p in small_primes:
        if p*p > m: break
        while m % p == 0:
            lpf = p; m //= p
    if m > 1:
        lpf = max(lpf, m)   # remaining cofactor is prime
    return lpf

def norm_of_signed_tuple(exps_signed, n):
    """
    S = sum eps_i * zeta_n^{a_i}, n=2^k.  N(S) = prod_{t odd, 1<=t<n} sigma_t(S),
    sigma_t(zeta)=zeta^t.  Compute exactly: sigma_t(S) = sum eps_i * zeta^{(a_i*t) mod n};
    represent each algebraic value as a complex with high precision is unsafe -> instead use the
    EXACT integer norm via resultant of the polynomial sum_i eps_i x^{a_i} with Phi_n(x)=x^{n/2}+1.
    """
    # build coefficient vector of P(x) = sum eps_i x^{a_i}  (degree < n)
    coeffs = [0]*n
    for (a, e) in exps_signed:
        coeffs[a] += e
    # Res(P, x^{n/2}+1).  Reduce P mod (x^{n/2}+1): x^{n/2} = -1.
    half = n//2
    red = [0]*half
    for a in range(n):
        if coeffs[a]:
            if a < half: red[a] += coeffs[a]
            else: red[a-half] -= coeffs[a]
    # red is the element of Z[zeta]/(x^{half}+1) as a vector. Its norm = Res(red(x), x^{half}+1)
    # = prod_{t odd} red(zeta^t).  Compute exactly via the circulant-like determinant: the norm of
    # a + sum c_i zeta^i in Z[zeta_{2 half}] equals det of multiplication-by-element matrix.
    return _norm_via_matrix(red, half)

def _norm_via_matrix(red, half):
    # element u = sum_{i<half} red[i] zeta^i in R=Z[x]/(x^half+1). Norm = det(M_u),
    # M_u[j][i] = coeff of zeta^j in (zeta^i * u). zeta^i * zeta^k = zeta^{i+k}, reduce x^half=-1.
    # Build half x half integer matrix, compute determinant exactly (fraction-free Bareiss).
    M = [[0]*half for _ in range(half)]
    for i in range(half):
        # column i = zeta^i * u
        for k in range(half):
            if red[k] == 0: continue
            idx = i + k
            sgn = 1
            if idx >= half:
                idx -= half; sgn = -1
            M[idx][i] += sgn*red[k]
    return _bareiss_det(M, half)

def _bareiss_det(M, n):
    M = [row[:] for row in M]
    sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            swap = None
            for i in range(k+1, n):
                if M[i][k] != 0: swap = i; break
            if swap is None: return 0
            M[k], M[swap] = M[swap], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
        prev = M[k][k]
    return sign*M[n-1][n-1]

def census(n, r, sample_cap=None):
    """Enumerate signed 2r-tuples (r '+' exponents, r '-' exponents) of mu_n, collect N(S) for S!=0."""
    half = n//2
    small_primes = primes_up_to(2_000_000)
    max_norm = 0
    max_lpf = 1
    zero_count = 0
    nonzero_norms = []
    cnt = 0
    import itertools, random
    total = n**(2*r)
    if sample_cap and total > sample_cap:
        rng = random.Random(12345)
        gen = ([rng.randrange(n) for _ in range(2*r)] for _ in range(sample_cap))
        sampled = True
    else:
        gen = product(range(n), repeat=2*r)
        sampled = False
    for tup in gen:
        plus = tup[:r]; minus = tup[r:]
        es = [(a, 1) for a in plus] + [(a, -1) for a in minus]
        N = norm_of_signed_tuple(es, n)
        cnt += 1
        if N == 0:
            zero_count += 1
        else:
            aN = abs(N)
            if aN > max_norm: max_norm = aN
            lpf = largest_prime_factor(aN, small_primes)
            if lpf > max_lpf: max_lpf = lpf
            nonzero_norms.append(aN)
    return dict(n=n, r=r, sampled=sampled, scanned=cnt, zero=zero_count,
               max_norm=max_norm, max_lpf=max_lpf,
               naive=(2*r)**half)

if __name__ == "__main__":
    print("="*96)
    print("WRAP NORM CENSUS: largest prime that can divide N(S) for a nonzero signed 2r-tuple of mu_n.")
    print("  T(n,r)=max prime factor over all N(S) = the EXACT wrap threshold (A_r=0 for all p>T).")
    print("  Compare T(n,r) to naive (2r)^{phi(n)} and to the prize band n^4..n^5.")
    print("="*96)
    # feasible exact full enumeration: n^{2r} not too big and half x half det cheap.
    configs = [
        (4, 2), (4, 3),
        (8, 2), (8, 3),
        (16, 2),
    ]
    for (n, r) in configs:
        cap = 400000
        res = census(n, r, sample_cap=cap)
        T = res['max_lpf']
        n4 = n**4; n5 = n**5
        betaT = math.log(T)/math.log(n) if T > 1 else 0.0
        tag = "SAMPLED" if res['sampled'] else "FULL"
        print(f"  n={n:>2} r={r} [{tag} {res['scanned']} tuples, {res['zero']} char0-zero]:")
        print(f"     max|N(S)| = {res['max_norm']:.3e}   naive (2r)^{n//2} = {res['naive']:.3e}")
        print(f"     T(n,r)=max prime factor = {T}  (~ n^{betaT:.2f})   prize band n^4={n4:.2e} n^5={n5:.2e}")
        verdict = ("BELOW prize band -> anomaly structurally absent in prize regime"
                   if T < n4 else
                   "AT/ABOVE prize band -> anomaly alive; height alone gives no gain")
        print(f"     => T {'<' if T<n4 else '>='} n^4 :  {verdict}")
        print()

#!/usr/bin/env python3
"""
#407 OPEN ITEM: constant-index large-subgroup additive energy A_k structural bound.

Goal: decisively determine, via FFT, whether the implied constant C in
   A_k := E_k(mu_n) - n^{2k}/p  <=  C^k * k! * n^k
is BOUNDED as n grows at FIXED large index m=(p-1)/n, for k=2..6.

Exact identities used (all verified inline):
  - eta_b := sum_{x in mu_n} e_p(b x)  (Gauss period, b in Z/p)
  - E_k = #{(x_1..x_k,y_1..y_k) in mu_n^{2k} : sum x = sum y}
        = (1/p) * sum_b |eta_b|^{2k}
  - b=0 term: |eta_0|^{2k} = n^{2k}, contributes n^{2k}/p
  - so  A_k := E_k - n^{2k}/p = (1/p) * sum_{b != 0} |eta_b|^{2k}   <-- the 2k-th moment of sup-norm

FFT route to E_k WITHOUT forming eta (which is O(p) complex, fine up to p~1e7):
  r(s) = #{ k-tuples from mu_n summing to s }  (s in Z/p)
       = (k-fold cyclic convolution of indicator(mu_n))
  E_k = sum_s r(s)^2.
  We compute r via repeated FFT-convolution of the indicator over Z/p (length p).
  This is exact in integer arithmetic if we round (counts are integers < n^k).

We compute, for each (n, m):
  p = m*n + 1 (smallest prime of that form for the given m, n -- index exactly m)
  M(n) = max_{b!=0}|eta_b|            (the sup-norm / L^inf face)
  A_k for k=2..6
  ratio_k := A_k / (k! * n^k)   ->  the implied C^k; report C_k := ratio_k^{1/k}
Also the trivial-mode (j=0) subtraction: note A_k already subtracts the b=0 term.

DECISION CRITERION:
  - If C_k (=ratio_k^{1/k}) is BOUNDED (flat or decreasing) as n grows at fixed m, and across k,
    the structural bound holds -> potential closure lane.
  - If C_k GROWS with n (esp. like sqrt(log p) i.e. the sup-norm), it FOLDS TO BGK:
    A_k >= M(n)^{2k}/p * (something), and M(n) ~ sqrt(n log p) would force C_k ~ sqrt(log p) growth.
"""
import numpy as np
import math
from collections import Counter

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primroot(p):
    # find a primitive root mod p (p prime)
    if p == 2: return 1
    phi = p - 1
    # factor phi
    fs = []
    m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    for a in range(2, p):
        if all(pow(a, phi//q, p) != 1 for q in fs):
            return a
    return None

def subgroup(p, n):
    """the unique order-n multiplicative subgroup mu_n < F_p^*  (n | p-1)."""
    g0 = primroot(p)
    g = pow(g0, (p-1)//n, p)
    dom = set()
    x = 1
    for _ in range(n):
        dom.add(x)
        x = x*g % p
    assert len(dom) == n, (p, n, len(dom))
    return sorted(dom)

def eta_all(p, dom):
    """eta_b = sum_{x in dom} exp(2pi i b x / p), for all b in 0..p-1, via one FFT of indicator."""
    ind = np.zeros(p)
    for x in dom: ind[x] = 1.0
    # eta_b = sum_x ind[x] exp(2pi i b x/p) = (DFT of ind)[b] with sign convention e^{+}
    # np.fft.fft uses e^{-2pi i b x/p}; conj or sign of b doesn't change |eta_b|.
    F = np.fft.fft(ind)
    return F  # |F[b]| = |eta_b|

def energy_via_fft(p, dom, k):
    """E_k = sum_s r(s)^2, r = k-fold cyclic conv of indicator over Z/p. Exact (integer)."""
    ind = np.zeros(p)
    for x in dom: ind[x] = 1.0
    F = np.fft.fft(ind)
    Fk = F**k            # FFT of k-fold convolution
    r = np.fft.ifft(Fk).real
    r = np.rint(r)       # counts are integers
    Ek = float(np.sum(r*r))
    return Ek

def run(cases, ks=(2,3,4,5,6), pmax=12_000_000):
    print(f"# constant-index A_k structural-bound probe; A_k=E_k - n^{{2k}}/p = (1/p)sum_{{b!=0}}|eta_b|^{{2k}}")
    print(f"# ratio_k = A_k/(k! n^k); C_k = ratio_k^(1/k) is the IMPLIED constant. Bounded C_k => closure; growing => BGK.")
    hdr = f"{'n':>7} {'m':>5} {'p':>11} {'M/sqrt(n)':>10} {'M/sqrtnlogp':>11} | "
    hdr += " ".join(f"{'C'+str(k):>7}" for k in ks)
    print(hdr)
    rows = []
    for (n, m) in cases:
        # smallest prime p = m*n + 1  (index exactly m, subgroup order exactly n)
        p = m*n + 1
        # we want index EXACTLY m, so p-1 = m*n -> p=mn+1; require prime
        if not isprime(p):
            # bump m by smallest t so that t*n+1 prime, index = t (still "near" m). Skip if can't keep index.
            # To keep index FIXED we must keep m; just skip non-prime mn+1.
            continue
        if p > pmax:
            continue
        dom = subgroup(p, n)
        F = eta_all(p, dom)
        absF = np.abs(F)
        M = float(np.max(absF[1:]))           # sup over b!=0
        logp = math.log(p)
        cstrs = []
        for k in ks:
            Ek = energy_via_fft(p, dom, k)
            Ak = Ek - (n**(2*k))/p
            ratio = Ak / (math.factorial(k) * (n**k))
            Ck = ratio**(1.0/k) if ratio > 0 else 0.0
            cstrs.append(Ck)
        rows.append((n, m, p, M, cstrs))
        line = f"{n:>7} {m:>5} {p:>11} {M/math.sqrt(n):>10.3f} {M/math.sqrt(n*logp):>11.3f} | "
        line += " ".join(f"{c:>7.3f}" for c in cstrs)
        print(line, flush=True)
    return rows

if __name__ == "__main__":
    print("="*100)
    print("PART A: fixed SMALL index m=2 (QR-like), n=2^mu growing. Subgroup order n=(p-1)/2.")
    print("="*100)
    casesA = [(2**mu, 2) for mu in range(3, 22)]
    runA = run(casesA)

    print()
    print("="*100)
    print("PART B: fixed index m=4, n=2^mu growing.")
    print("="*100)
    casesB = [(2**mu, 4) for mu in range(3, 21)]
    run(casesB)

    print()
    print("="*100)
    print("PART C: fixed LARGER index m=16, n=2^mu growing  (the 'fixed large index' the directive asks).")
    print("="*100)
    casesC = [(2**mu, 16) for mu in range(3, 19)]
    run(casesC)

    print()
    print("="*100)
    print("PART D: fixed index m=64, n=2^mu growing.")
    print("="*100)
    casesD = [(2**mu, 64) for mu in range(3, 17)]
    run(casesD)

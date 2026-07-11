#!/usr/bin/env python3
"""
#407 OPEN ITEM: constant-index large-subgroup additive energy A_k structural bound.

Decisively determine via FFT whether the IMPLIED constant C in
   A_k := E_k(mu_n) - n^{2k}/p  <=  C^k * k! * n^k
is BOUNDED as n grows at FIXED index m=(p-1)/n, for k=2..6.

Exact identity (verified): with eta_b = sum_{x in mu_n} e_p(b x),
   A_k = E_k - n^{2k}/p = (1/p) * sum_{b != 0} |eta_b|^{2k}      (2k-th moment of the sup-norm)

PRECISION-SAFE: we compute A_k DIRECTLY as (1/p) sum_{b!=0} |eta_b|^{2k} from |eta_b|
(which are O(sqrt(p)) ~ O(sqrt(mn)) ), NOT via the catastrophic-cancellation E_k - n^{2k}/p.
|eta_b| computed by ONE numpy FFT of the indicator (exact to ~1e-9 relative).

Two family designs:
  (1) SMALLEST index: p = smallest prime = 1 mod n  -> index m grows slowly (~log).
  (2) FIXED index m: p = m*n+1 when prime (sparse for n=2^mu).
We report:
  M(n) = max_{b!=0}|eta_b|        (L^inf face)
  C_k := (A_k/(k! n^k))^{1/k}     (implied constant; bounded => closure, ~sqrt(log p) => BGK)
  ALSO the SUP-NORM-DRIVEN lower bound on C_k: since A_k >= |eta_b*|^{2k}/p = M^{2k}/p,
       C_k >= (M^{2k}/(p k! n^k))^{1/k} = M^2/( (p k! n^k)^{1/k} ).  We print both
       to see whether A_k is dominated by the single sup-norm mode (=> folds to BGK)
       or is a genuine multi-mode average (=> structural, possibly closable).
"""
import numpy as np
import math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def primroot(p):
    if p == 2: return 1
    phi = p - 1
    fs = []; m = phi; d = 2
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
    g0 = primroot(p)
    g = pow(g0, (p-1)//n, p)
    dom = []
    x = 1
    for _ in range(n):
        dom.append(x); x = x*g % p
    assert len(set(dom)) == n
    return dom

def abs_eta(p, dom):
    ind = np.zeros(p, dtype=np.float64)
    for x in dom: ind[x] = 1.0
    F = np.fft.fft(ind)
    return np.abs(F)   # |eta_b|, b=0..p-1

def smallest_prime_1modn(n, start=None):
    p = (start if start else (n+1))
    # make p = 1 mod n
    p = ((p - 1)//n + 1)*n + 1 if (p-1) % n != 0 else p
    if p < n+1: p = n+1
    p = ((n) ) + 1
    while not isprime(p):
        p += n
    return p

def analyze(n, p, ks):
    dom = subgroup(p, n)
    A = abs_eta(p, dom)
    M = float(np.max(A[1:]))
    # tail sum over b!=0 of A^{2k}
    A2 = A[1:].astype(np.float64)**2   # |eta_b|^2 for b!=0
    out = {}
    logp = math.log(p)
    for k in ks:
        # A_k = (1/p) sum_{b!=0} (|eta|^2)^k
        Ak = float(np.sum(A2**k)) / p
        ratio = Ak / (math.factorial(k) * (n**k))
        Ck = ratio**(1.0/k) if ratio > 0 else 0.0
        # sup-norm-only lower bound on C_k (single dominant mode):
        Ak_lb = (M**(2*k)) / p
        ratio_lb = Ak_lb / (math.factorial(k) * (n**k))
        Ck_lb = ratio_lb**(1.0/k) if ratio_lb > 0 else 0.0
        out[k] = (Ck, Ck_lb, Ak)
    return M, out, logp

def run_smallest_index(mus, ks=(2,3,4,5,6), pmax=20_000_000):
    print("# FAMILY 1: smallest prime p = 1 mod n, n=2^mu  (index m = (p-1)/n grows slowly)")
    print(f"{'n':>8} {'m':>6} {'p':>11} {'M/sqrtn':>8} {'M/sq(nlnp)':>10} | " +
          " ".join(f"C{k}(/lb)".rjust(13) for k in ks))
    for mu in mus:
        n = 2**mu
        p = smallest_prime_1modn(n)
        if p > pmax: continue
        m = (p-1)//n
        M, out, logp = analyze(n, p, ks)
        cells = []
        for k in ks:
            Ck, Ck_lb, _ = out[k]
            cells.append(f"{Ck:.3f}/{Ck_lb:.3f}".rjust(13))
        print(f"{n:>8} {m:>6} {p:>11} {M/math.sqrt(n):>8.3f} {M/math.sqrt(n*logp):>10.3f} | " +
              " ".join(cells), flush=True)

def run_fixed_index(m, mus, ks=(2,3,4,5,6), pmax=20_000_000):
    print(f"# FAMILY 2: FIXED index m={m}: p=m*n+1 when prime, n=2^mu")
    print(f"{'n':>8} {'m':>6} {'p':>11} {'M/sqrtn':>8} {'M/sq(nlnp)':>10} | " +
          " ".join(f"C{k}(/lb)".rjust(13) for k in ks))
    for mu in mus:
        n = 2**mu
        p = m*n + 1
        if not isprime(p): continue
        if p > pmax: continue
        M, out, logp = analyze(n, p, ks)
        cells = []
        for k in ks:
            Ck, Ck_lb, _ = out[k]
            cells.append(f"{Ck:.3f}/{Ck_lb:.3f}".rjust(13))
        print(f"{n:>8} {m:>6} {p:>11} {M/math.sqrt(n):>8.3f} {M/math.sqrt(n*logp):>10.3f} | " +
              " ".join(cells), flush=True)

if __name__ == "__main__":
    print("="*120)
    print("Implied constant C_k = (A_k/(k! n^k))^{1/k}.  cell = C_k / Ck_lb  (lb = sup-norm-only lower bound).")
    print("Bounded C_k as n grows at fixed m  =>  STRUCTURAL closure.   C_k ~ sqrt(log p)  =>  FOLDS TO BGK.")
    print("If C_k ~ Ck_lb (ratio ~1) the moment is sup-norm-DOMINATED (single mode) => BGK.")
    print("="*120)
    run_smallest_index(range(3, 24))
    print()
    for m in (2, 4, 16, 64):
        run_fixed_index(m, range(3, 22))
        print()

"""
probe_wfLA_beta4_growth.py  (lane wf-LA): the n-dependence of C(n) at the EXACT prize slice beta=4.

We hold beta = log_n(p) ~= 4 (the prize lower edge, p ~ n^4) and ask: as n grows, does
C(n) = M / sqrt(n*log(p/n))  stay bounded by a small constant, or does it creep?

If C(n) is BOUNDED (and small) at beta=4 for the deterministic mu_n family, that is the EFFECTIVE
near-Ramanujan-up-to-sqrt-log statement the prize needs (C = O(1)).  If it creeps like sqrt(log n)
or a power, the prize constant is not uniform.  We also report M/sqrt(n) (raw spectral ratio) and
M/(2 sqrt(n*log(p/n))) to compare with the in-tree C=2 ceiling.

FFT bound: p ~ n^4, so n<=2^5=32 (p~1e6) feasible exactly; n=64 -> p~1.7e7 (FFT ~ 0.7s, OK).
For n=128 (p~2.7e8) full FFT is 2GB+ -- we instead use a DIRECT worst-b search over a sample of b
plus the m-coset structure (from probe A, worst b unstructured, so random sample is fair).
"""
import math, sys, os, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import Workspace, isprime, subgroup

def Cfun(n, p, M): return M / math.sqrt(n * math.log(p / n))

def prime_at_beta(n, beta, lo_mult=0.9):
    """find prime p = n*m+1 closest to n^beta (m chosen so p ~ n^beta)."""
    target = n ** beta
    m0 = max(1, int(round(target / n)))
    for d in range(0, 200000):
        for m in (m0 + d, m0 - d):
            if m < 1: continue
            p = n*m + 1
            if isprime(p):
                return m, p
    return None, None

print("="*78)
print("C(n) at the prize slice beta=log_n(p)~=4 (FFT-exact M, n<=64)")
print("="*78)
print(f"{'n':>6} {'p':>14} {'beta':>5} {'M':>9} {'M/sqrtn':>8} {'C':>6} {'C/2':>6} {'C/sqrtlog_n':>11}")
rows=[]
for mu in range(2, 7):  # n=4..64
    n = 1<<mu
    m, p = prime_at_beta(n, 4.0)
    if p is None or n*p > 2_000_000_000:
        print(f"{n:>6}  (skip: p too large)")
        continue
    if p > 30_000_000:
        print(f"{n:>6}  (skip FFT: p={p}>3e7)")
        continue
    t=time.time()
    W = Workspace(n, p)
    M = W.M
    C = Cfun(n, p, M)
    rows.append((n, C))
    print(f"{n:>6} {p:>14} {math.log(p)/math.log(n):>5.2f} {M:>9.2f} {W.M_over_sqrt_n:>8.3f} "
          f"{C:>6.3f} {C/2:>6.3f} {C/math.sqrt(math.log(n)):>11.3f}  ({time.time()-t:.1f}s)")

print("\nGrowth check: if C ~ a + b*sqrt(log n), fit; if C ~ a*n^c, fit.")
if len(rows) >= 3:
    ns = np.array([r[0] for r in rows], float)
    Cs = np.array([r[1] for r in rows], float)
    # fit C = a + b*sqrt(log n)
    X = np.vstack([np.ones_like(ns), np.sqrt(np.log(ns))]).T
    coef, *_ = np.linalg.lstsq(X, Cs, rcond=None)
    pred = X@coef
    print(f"  C ~ {coef[0]:.3f} + {coef[1]:.3f}*sqrt(log n)   resid={np.abs(Cs-pred).max():.4f}")
    # fit log C = log a + c log n
    lc, *_ = np.linalg.lstsq(np.vstack([np.ones_like(ns), np.log(ns)]).T, np.log(Cs), rcond=None)
    print(f"  C ~ {math.exp(lc[0]):.3f} * n^{lc[1]:.4f}   (power-law exponent; ~0 => bounded)")

print()
print("="*78)
print("Same slice at beta=5 (deep prize) and beta=4.5 -- compare constant across the prize band")
print("="*78)
for b in (4.5, 5.0):
    print(f"-- beta={b} --")
    for mu in range(2, 6):
        n=1<<mu
        m,p = prime_at_beta(n, b)
        if p is None or p > 30_000_000:
            print(f"   n={n}: skip (p={p})"); continue
        W=Workspace(n,p); M=W.M; C=Cfun(n,p,M)
        print(f"   n={n:>4} p={p:>12} beta={math.log(p)/math.log(n):.2f} M/sqrtn={W.M_over_sqrt_n:.3f} C={C:.3f}")

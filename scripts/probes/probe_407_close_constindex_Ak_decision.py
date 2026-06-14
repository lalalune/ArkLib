#!/usr/bin/env python3
"""
#407 DECISION probe: is the implied constant C in  A_k <= C^k k! n^k  BOUNDED at fixed index,
or does it secretly fold to BGK (carry a sqrt(log p) factor)?

THE CLEAN TEST. The structural conjecture A_k <= C^k k! n^k with C ABSOLUTE is equivalent
(for the dominant-tail behavior) to the SUB-GAUSSIAN sup-norm bound
   M(n) := max_{b!=0}|eta_b| <= C' * sqrt(n)      (n-scale, NO log) ?
versus the BGK/Paley sub-Gaussian bound
   M(n) <= C'' * sqrt(n log p)                    (log-scale) ?

WHY: A_k = (1/p) sum_{b!=0}|eta_b|^{2k}.  If |eta_b| had a sub-GAUSSIAN tail
   #{b : |eta_b| > t sqrt(n)} <~ p * exp(-t^2/2),  then
   A_k = (1/p) integral ... ~ (2k-1)!! n^k  (the Wick/Gaussian value),  => C bounded (~e/2), k-indep.
But the EXTREME mode M(n) controls whether the LAST few k are still Gaussian:
   A_k >= M^{2k}/p.  For this to stay <= C^k k! n^k for ALL k up to k~log p we need
   M^2/p^{1/k} <= C k!^{1/k} n  i.e. M <= C' sqrt(n) * p^{1/(2k)} ... at k~log p, p^{1/(2k)}=O(1).
So: C bounded for ALL k (incl k~log p)  <=>  M(n) <= C' sqrt(n)   (the FALSE Paley-graph-Ramanujan
bound -- known to require Paley Graph Conjecture, OPEN).
If instead only M <= C' sqrt(n log p) (BGK, also open but weaker), then at k~log p,
   A_k contribution from the top mode ~ (n log p)^k / p, and C_k ~ sqrt(log p) -> UNBOUNDED in p.

So the experiment that DECIDES: at fixed index m, does max_b|eta_b|/sqrt(n) stay bounded,
or grow like sqrt(log p) ~ sqrt(log(mn)) ~ sqrt(log n)?  Regress log(M/sqrt(n)) on log log p.
ALSO: directly does C_k for the LARGEST feasible k grow with n at fixed m?
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
    phi = p - 1; fs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    for a in range(2, p):
        if all(pow(a, phi//q, p) != 1 for q in fs): return a

def subgroup(p, n):
    g = pow(primroot(p), (p-1)//n, p)
    dom = []; x = 1
    for _ in range(n): dom.append(x); x = x*g % p
    return dom

def abs_eta(p, dom):
    ind = np.zeros(p, dtype=np.float64)
    for x in dom: ind[x] = 1.0
    return np.abs(np.fft.fft(ind))

# ---- Collect ALL feasible (n=2^mu) at a given index m: need p=mn+1 prime. ----
# To get MANY points at "fixed large index", relax: for each n, take the smallest index t>=m_target
# with t*n+1 prime, AND record actual t.  Then bin by t-band and look at trend in n.

def collect(mu_range, m_target, pmax=30_000_000, m_window=4.0):
    rows = []
    for mu in mu_range:
        n = 2**mu
        # find smallest t >= m_target with t*n+1 prime and within window [m_target, m_target*m_window]
        t = m_target
        p = None
        while t <= m_target*m_window:
            cand = t*n + 1
            if cand > pmax: break
            if isprime(cand):
                p = cand; break
            t += 1
        if p is None: continue
        dom = subgroup(p, n)
        A = abs_eta(p, dom)
        M = float(np.max(A[1:]))
        A2 = A[1:]**2
        ks = [k for k in range(2, 9)]
        Ck = {}
        for k in ks:
            Ak = float(np.sum(A2**k)) / p
            ratio = Ak / (math.factorial(k) * (n**k))
            Ck[k] = ratio**(1.0/k) if ratio > 0 else float('nan')
        rows.append((n, t, p, M, Ck))
    return rows

def report(m_target, mu_range):
    print("="*110)
    print(f"FIXED-INDEX band around m~{m_target}: trend of M/sqrt(n), M/sqrt(n logp), and C_k vs n")
    print("="*110)
    rows = collect(mu_range, m_target)
    print(f"{'mu':>3} {'n':>9} {'idx':>4} {'p':>11} {'M/sqn':>7} {'M/sq(nlnp)':>10} {'M/sq(nlnn)':>10} | C2..C8")
    Ms=[]; ns=[]; ps=[]
    for (n,t,p,M,Ck) in rows:
        lnp=math.log(p); lnn=math.log(n)
        cs=" ".join(f"{Ck[k]:.3f}" for k in range(2,9))
        print(f"{int(math.log2(n)):>3} {n:>9} {t:>4} {p:>11} {M/math.sqrt(n):>7.3f} "
              f"{M/math.sqrt(n*lnp):>10.3f} {M/math.sqrt(n*max(lnn,1)):>10.3f} | {cs}", flush=True)
        Ms.append(M); ns.append(n); ps.append(p)
    if len(Ms) >= 4:
        Ms=np.array(Ms); ns=np.array(ns,dtype=float); ps=np.array(ps,dtype=float)
        y = np.log(Ms/np.sqrt(ns))          # log(M/sqrt n)
        # regress y on log(log p): slope ~0.5 => M ~ sqrt(n log p) (BGK); slope ~0 => M~sqrt(n) (Ramanujan)
        x1 = np.log(np.log(ps))
        A = np.vstack([x1, np.ones_like(x1)]).T
        s1,_,_,_ = np.linalg.lstsq(A, y, rcond=None)
        # also regress on log n
        x2 = np.log(np.log(ns))
        A2 = np.vstack([x2, np.ones_like(x2)]).T
        s2,_,_,_ = np.linalg.lstsq(A2, y, rcond=None)
        print(f"  REGRESSION log(M/sqrt n) ~ a*log(log p): slope a = {s1[0]:+.3f}  "
              f"(a~0.5 => BGK sqrt(n log p); a~0 => bounded/Ramanujan sqrt n)")
        print(f"  REGRESSION log(M/sqrt n) ~ a*log(log n): slope a = {s2[0]:+.3f}")
    print()

if __name__ == "__main__":
    print("KEY: C_k BOUNDED for all k up to ~log p  <=>  M(n) <= C sqrt(n)  (Paley/Ramanujan, OPEN).")
    print("     If M ~ sqrt(n log p) (BGK), then C_k -> grows ~ sqrt(log p) at k ~ log p.")
    print("     Regression slope of log(M/sqrt n) on log(log p): 0.5 = BGK, 0.0 = bounded.")
    print()
    for m in (2, 4, 8, 16, 64):
        report(m, range(3, 25))

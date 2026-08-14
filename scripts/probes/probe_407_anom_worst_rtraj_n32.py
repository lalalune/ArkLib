#!/usr/bin/env python3
"""
#407 ANOMALY SUPPRESSION at n=32 -- worst-in-window-bad-prime FULL r-trajectory (lean engine).

EDGE (uncontested, board state 2026-06-15 ~06:1x):
  - DC-subtracted A_r <= Wick is THE open carrier (raw E_r<=Wick FALSE n>=64; PairingResidualFailsAtPrize).
  - ec140aead (n=16, worst in-window bad prime p=76001): proxy Anom_r<=n^{2r}/p FAILS deep-r (crosses 1 @ r=6)
    but the TARGET A_r<=Wick survives. r-axis pinned AT n=16.
  - 98db97afc (n=32..256, A_r/Wick): monotone collapse, no catch-up -- BUT at a GENERIC prime (p~2^24), which
    UNDERSTATES the anomaly. Not the adversarial (worst in-window bad) prime.
  - GAP: combine worst-in-window-bad-prime x full-r-trajectory x n=32. This probe does that.

ENGINE (exact integer counts):
  E_r^(p) = #{(a,b) in mu_n^{2r}: sum a = sum b mod p}  via r-fold mod-p convolution then sum-of-squares.
  E_r^(0) = char-0 ring count via lattice Z^{n/2} convolution (zeta^{n/2}=-1, n=2^a).
  Anom_r = E_r^(p) - E_r^(0).  Wick = (2r-1)!!*n^r.  A_r = E_r^(p) - n^{2r}/p.
  TARGET A_r<=Wick.  PROXY Anom_r<=n^{2r}/p.
RULE-2 proper mu_n, p>=n^4, never n=q-1. RULE-1 pure-python exact => axiom-clean. RULE-6 sub-prize p; maps
the worst-in-window trajectory, does NOT prove forall-field asymptotic (BGK). No CORE closure.
"""
import math
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    if m % 3 == 0: return m == 3
    d = 5
    while d*d <= m:
        if m % d == 0 or m % (d+2) == 0: return False
        d += 6
    return True

def prime_factors(m):
    f = set(); d = 2
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f

def primroot(p):
    fs = prime_factors(p-1); g = 2
    while any(pow(g, (p-1)//q, p) == 1 for q in fs): g += 1
    return g

def roots_modp(n, p):
    g = primroot(p); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def Ep(mu, p, r):
    """E_r^(p): r-fold convolution of the single-draw residue distribution, sum of squared bucket counts."""
    base = Counter()
    for x in mu: base[x % p] += 1
    items = list(base.items())
    dist = {0: 1}
    for _ in range(r):
        nd = {}
        for s, c in dist.items():
            for x, cx in items:
                k = s + x
                if k >= p: k -= p
                nd[k] = nd.get(k, 0) + c*cx
        dist = nd
    return sum(c*c for c in dist.values())

def lattice_vec(e, n):
    phi = n // 2; v = [0]*phi
    if e < phi: v[e] += 1
    else: v[e-phi] -= 1
    return tuple(v)

_E0_cache = {}
def E0_ring(n, r):
    if (n, r) in _E0_cache: return _E0_cache[(n, r)]
    base = Counter()
    for e in range(n): base[lattice_vec(e, n)] += 1
    items = list(base.items())
    dist = {tuple([0]*(n//2)): 1}
    for _ in range(r):
        nd = {}
        for v, c in dist.items():
            for u, cu in items:
                w = tuple(v[i]+u[i] for i in range(len(v)))
                nd[w] = nd.get(w, 0) + c*cu
        dist = nd
    val = sum(c*c for c in dist.values())
    _E0_cache[(n, r)] = val
    return val

def doublefact_odd(m):
    r = 1; k = m
    while k > 0: r *= k; k -= 2
    return r

def wick(n, r): return doublefact_odd(2*r-1) * (n**r)

def rstar(p): return max(2, round(math.log(p)))

def find_worst_inwindow_bad_prime(n, r_anchor, beta_lo=4.0, n_primes_scan=400):
    """Scan in-window primes p in [n^4, ...] with p-1 divisible by n (proper mu_n). For each, compute
       Anom_{r_anchor}(p) exactly; keep the one with max proxy-ratio Anom/(n^{2r}/p). 'Worst' = max anomaly."""
    lo = int(n**beta_lo)
    E0a = E0_ring(n, r_anchor)
    m = (lo // n) + 1
    if m < 2: m = 2
    scanned = 0; best = None; bad_count = 0
    while scanned < n_primes_scan:
        p = m*n + 1; m += 1
        if p <= lo or not is_prime(p): continue
        scanned += 1
        mu = roots_modp(n, p)
        Epp = Ep(mu, p, r_anchor)
        anom = Epp - E0a
        if anom > 0:
            bad_count += 1
            ratio = anom / ((n**(2*r_anchor))/p)
            if best is None or ratio > best[1]:
                best = (p, ratio, anom, Epp, E0a)
    return best, scanned, bad_count

def run(n, r_anchor, rmax_cap=6):
    print(f"\n========== n={n} (2-power) worst-in-window-bad-prime r-trajectory ==========")
    print(f"scanning in-window primes (anchor r={r_anchor}) for the worst (max-anomaly) bad prime...")
    best, scanned, bad_count = find_worst_inwindow_bad_prime(n, r_anchor)
    if best is None:
        print(f"  NO in-window bad prime in {scanned} scanned (window clean at r={r_anchor})")
        return None
    p, ratio_a, anom_a, Epp_a, E0_a = best
    beta = math.log(p)/math.log(n)
    rs = min(rstar(p), rmax_cap)
    print(f"  scanned {scanned} in-window primes, {bad_count} bad; WORST: p={p} beta={beta:.3f} (anchor ratio={ratio_a:.4f})")
    print(f"  r*=round(ln p)={rstar(p)}  (capped at r={rs} for E0-ring tractability)")
    print(f"  {'r':>3} {'Anom_r':>16} {'n^2r/p':>16} {'proxy':>9} {'A_r/Wick':>10} {'E0/Wick':>10} {'TGT':>6}")
    mu = roots_modp(n, p)
    target_ok = True; proxy_ok = True; rows = []
    for r in range(2, rs+1):
        Epp = Ep(mu, p, r); E0 = E0_ring(n, r)
        anom = Epp - E0; W = wick(n, r); nb = (n**(2*r))/p
        A_r = Epp - (n**(2*r))/p
        pr = anom/nb; aw = A_r/W; ew = E0/W
        tgt = "OK" if aw <= 1.0 else "CRACK"
        if aw > 1.0: target_ok = False
        if pr > 1.0: proxy_ok = False
        print(f"  {r:>3} {anom:>16} {nb:>16.2f} {pr:>9.4f} {aw:>10.4f} {ew:>10.4f} {tgt:>6}")
        rows.append((r, anom, pr, aw, ew, tgt))
    print(f"  => PROXY Anom_r<=n^2r/p : {'SURVIVES' if proxy_ok else 'FAILS (crosses 1)'}")
    print(f"  => TARGET A_r<=Wick     : {'SURVIVES (all<=1)' if target_ok else 'CRACKS !!'}")
    return {"n": n, "p": p, "beta": beta, "rows": rows, "target_ok": target_ok, "proxy_ok": proxy_ok}

if __name__ == "__main__":
    res16 = run(16, r_anchor=4, rmax_cap=6)   # self-check vs ec140aead
    res32 = run(32, r_anchor=2, rmax_cap=6)   # THE EDGE

# --- extended n=32 search: wider prime window + higher anchor r (bad primes sit higher for n=32) ---
def run_wide(n, r_anchor, beta_lo, n_primes_scan, rmax_cap=6):
    print(f"\n========== n={n} WIDE scan: anchor r={r_anchor}, beta_lo={beta_lo}, scan={n_primes_scan} ==========")
    best, scanned, bad_count = find_worst_inwindow_bad_prime(n, r_anchor, beta_lo=beta_lo, n_primes_scan=n_primes_scan)
    if best is None:
        print(f"  NO bad prime in {scanned} scanned at r={r_anchor} beta_lo={beta_lo}"); return None
    p, ratio_a, anom_a, _, _ = best
    beta = math.log(p)/math.log(n); rs = min(rstar(p), rmax_cap)
    print(f"  scanned {scanned}, {bad_count} bad; WORST p={p} beta={beta:.3f} anchor-ratio={ratio_a:.4f} r*={rstar(p)} cap r={rs}")
    print(f"  {'r':>3} {'Anom_r':>18} {'n^2r/p':>18} {'proxy':>9} {'A_r/Wick':>10} {'E0/Wick':>10} {'TGT':>6}")
    mu = roots_modp(n, p); target_ok=True; proxy_ok=True
    for r in range(2, rs+1):
        Epp=Ep(mu,p,r); E0=E0_ring(n,r); anom=Epp-E0; W=wick(n,r); nb=(n**(2*r))/p
        A_r=Epp-(n**(2*r))/p; pr=anom/nb; aw=A_r/W; ew=E0/W
        tgt="OK" if aw<=1.0 else "CRACK"
        if aw>1.0: target_ok=False
        if pr>1.0: proxy_ok=False
        print(f"  {r:>3} {anom:>18} {nb:>18.2f} {pr:>9.4f} {aw:>10.4f} {ew:>10.4f} {tgt:>6}")
    print(f"  => PROXY: {'SURVIVES' if proxy_ok else 'FAILS'}   TARGET A_r<=Wick: {'SURVIVES' if target_ok else 'CRACKS !!'}")
    return {"n":n,"p":p,"beta":beta,"target_ok":target_ok,"proxy_ok":proxy_ok}

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "wide":
        # n=32: bad primes onset higher; scan more primes, try anchor r=3 (onset lower-beta as r grows past 2)
        run_wide(32, r_anchor=3, beta_lo=4.0, n_primes_scan=1500, rmax_cap=6)

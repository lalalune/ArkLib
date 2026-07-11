#!/usr/bin/env python3
"""
probe_dooriv_sixth_cumulant_multiprime.py  (#444, door-(iv) Lane 1) -- CONFIRMATION pass.

Sweep 1 (probe_dooriv_sixth_connected_cumulant.py) found g3 (normalized 6th connected cumulant
of the period marginal eta_b) collapsing toward 0 with n, with one finite-size wiggle at n=128.
This confirmation isolates finite-size/prime artifacts from a real signal by:
  (1) computing g2 (excess kurtosis) and g3 (6th cumulant) at MULTIPLE primes per n,
  (2) using the FULL quotient scan where feasible (n up to 64 fully; n=128,256 at >=3 primes,
      sampled identically so the comparison is apples-to-apples),
  (3) reporting the SPREAD across primes -- if g3 jitters around 0 with prime-dependent sign,
      it is finite-size noise (=> Gaussian, REFUTE the 6th-crack hope); if it is consistently
      bounded-away with stable sign, it is a real lever.

Honest framing: a vanishing marginal 6th cumulant means the period marginal is Gaussian to 6th
order -> no exploitable non-moment marginal structure at 6th. (It does NOT by itself bound the
SUP M(n); but it CLOSES the 'crack lives at 6th order' marginal hope flagged by commit 8b2df98a5.)
"""
import numpy as np
from math import sqrt

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prim_root(p):
    if p == 2: return 1
    phi = p-1; fac = set(); t = phi; d = 2
    while d*d <= t:
        while t % d == 0: fac.add(d); t //= d
        d += 1
    if t > 1: fac.add(t)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    raise RuntimeError

def primes_for(n, beta, count=3):
    """find `count` distinct primes p == 1 mod n, p > n^3, near n^beta."""
    out = []
    lo = max(int(round(n**beta)), n**3 + 1)
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while len(out) < count:
        if isprime(p):
            out.append(p)
        p += n
    return out

def periods(n, p, max_reps=120000, seed=777):
    g = prim_root(p)
    m = (p-1)//n
    H = np.array([pow(g, (m*j) % (p-1), p) for j in range(n)], dtype=np.int64)
    tp = 2.0*np.pi/p
    if m <= max_reps:
        ts = list(range(m)); sampled = False
    else:
        rng = np.random.default_rng(seed)
        ts = rng.choice(m, size=max_reps, replace=False); sampled = True
    # OVERFLOW-SAFE modular reduction (codex P2 fix): at n=256, p~4.3e9 => b*H can exceed int64.
    Hobj = H.astype(object)
    et = np.empty(len(ts))
    for i, t in enumerate(ts):
        b = pow(g, int(t), p)
        res = ((int(b) * Hobj) % p).astype(np.float64)
        et[i] = np.cos(tp * res).sum()
    return et, sampled

def cum(x):
    x = np.asarray(x, float); xc = x - x.mean()
    m2 = (xc**2).mean(); m4 = (xc**4).mean(); m6 = (xc**6).mean()
    k4 = m4 - 3*m2**2; k6 = m6 - 15*m4*m2 + 30*m2**3
    return k4/m2**2, k6/m2**3

def main():
    print("# door-(iv) 6th cumulant CONFIRMATION -- multiple primes per n")
    print("# Gaussian => g2,g3 -> 0. real lever => g3 stable-sign bounded-away across primes.\n")
    print(f"{'n':>5} {'beta':>5}  per-prime (g2, g3) ...        | g2 mean+/-sd      g3 mean+/-sd")
    for n in (16, 32, 64, 128, 256):
        beta = 4.0
        ps = primes_for(n, beta, count=3)
        g2s, g3s = [], []
        cell = []
        for p in ps:
            et, sm = periods(n, p)
            g2, g3 = cum(et)
            g2s.append(g2); g3s.append(g3)
            cell.append(f"({g2:+.3f},{g3:+.3f}){'~' if sm else ''}")
        g2m, g2sd = np.mean(g2s), np.std(g2s)
        g3m, g3sd = np.mean(g3s), np.std(g3s)
        print(f"{n:>5} {beta:>5.1f}  {'  '.join(cell):<40} | {g2m:+.4f}+/-{g2sd:.4f}  {g3m:+.4f}+/-{g3sd:.4f}")
    print("\nINTERPRETATION:")
    print("  - if g3 mean -> 0 AND its sign flips across primes (sd >= |mean|): finite-size noise,")
    print("    period marginal is GAUSSIAN to 6th order => 6th-cumulant door-(iv) lever REFUTED.")
    print("  - if g3 mean stays bounded-away with consistent sign (|mean| >> sd): real lever, probe on.")

if __name__ == "__main__":
    main()

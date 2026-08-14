#!/usr/bin/env python3
"""
probe_444_worstcoset_count_growth.py  (#444, door-(iv) Lane 1)

THE PRECISE UNANSWERED LANE-1 SLACK QUESTION
--------------------------------------------
Prior work pinned: the near-max set W(tau) = {b!=0 : |eta_b| >= (1-tau)*M(n)} is a UNION of full
mu_n-cosets (coset-closed, sign-symmetric) but ADDITIVELY SPREAD (|W+W|/|W| grows, no AP/square-class).
That characterizes W's *additive* structure. It did NOT pin the **number of distinct near-max cosets**
  Ncos(tau, n) = |W(tau)| / n
as a function of n. This count is the EXACT Lane-1 slack lever:

  - If Ncos -> 1 (a SINGLE worst coset, up to sign a constant O(1) cosets), the peak is ISOLATED:
    the worst-b alignment rho(b*) is forced toward 1 and there is NO room for a non-sum-product
    anti-concentration bound to grip (the mass is concentrated on O(1) cosets -> moment-equivalent).
  - If Ncos GROWS with n (many near-max cosets at fixed tau), the peak is DEGENERATE/SPREAD across
    many frequencies: a structure-sensitive small-ball bound could in principle exploit the spread
    of the worst-coset SET without routing through multiplicative energy.

This is a SINGLE sweep over n=16..256, multiple structured odd-m primes, drawing ONE verdict.
NO moment, NO completion, NO Lean. PROPER mu_n < F_p^*, p == 1 mod n, m=(p-1)/n ODD, never n=q-1.
"""
import math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    i = 5
    while i*i <= x:
        if x % i == 0 or x % (i+2) == 0: return False
        i += 6
    return True

def find_prime_thin(n, beta, odd_m=True):
    target = int(n**beta)
    p = target - (target % n) + 1
    if p <= target: p += n
    for _ in range(2000000):
        if isprime(p):
            mm = (p-1)//n
            if (mm % 2 == 1) or (not odd_m):
                return p
        p += n
    return None

def factor(x):
    fs = set(); d = 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x//=d
        d += 1
    if x > 1: fs.add(x)
    return fs

def generator(p):
    pm1 = p-1; fs = factor(pm1)
    for cand in range(2, p):
        if all(pow(cand, pm1//q, p) != 1 for q in fs):
            return cand
    return None

def subgroup(n, p, g):
    h = pow(g, (p-1)//n, p)
    return sorted(set(pow(h, i, p) for i in range(n)))

def eta_abs_sweep(mu, p):
    bs = np.arange(0, p, dtype=np.int64)
    acc = np.zeros(p, dtype=np.complex128)
    twopi = 2*math.pi
    for x in mu:
        acc += np.exp(1j * twopi * ((bs * x) % p) / p)
    return np.abs(acc)

def coset_count(W, mu, p):
    """number of distinct mu_n-cosets covered by frequency set W."""
    reps = set()
    muarr = mu
    for b in W:
        reps.add(min((b*x) % p for x in muarr))
    return len(reps)

def analyze(n, beta, rows):
    p = find_prime_thin(n, beta)
    if p is None:
        print(f"  [n={n} beta={beta}] no odd-m prime found", flush=True); return
    g = generator(p)
    mu = subgroup(n, p, g)
    if len(mu) != n:
        print(f"  [n={n}] |mu|={len(mu)}!=n skip", flush=True); return
    mm = (p-1)//n
    av = eta_abs_sweep(mu, p)
    av[0] = -1.0
    M = av.max(); sqrtn = math.sqrt(n)
    beff = math.log(p)/math.log(n)
    line = [f"n={n:4d} p={p:>12d} m{'_ODD' if mm%2 else 'even'} beff={beff:.2f} M/sqrtn={M/sqrtn:.2f}"]
    for tau in (0.02, 0.05, 0.10):
        thr = (1-tau)*M
        W = [int(b) for b in np.nonzero(av >= thr)[0]]
        ncos = coset_count(W, mu, p)
        rows.setdefault(tau, []).append((n, ncos))
        line.append(f"tau{int(tau*100):02d}:Ncos={ncos}")
    print("  " + "  ".join(line), flush=True)

if __name__ == "__main__":
    print("=== probe_444_worstcoset_count_growth: # distinct near-max cosets vs n ===", flush=True)
    rows = {}
    for n in (16, 32, 64, 128, 256):
        # use the smallest beta that yields an odd-m prime; try a couple
        done = False
        for beta in (4.0, 4.5, 5.0):
            p = find_prime_thin(n, beta)
            if p is not None:
                analyze(n, beta, rows); done = True; break
        if not done:
            print(f"  [n={n}] skipped (no prime)", flush=True)
    print("\n--- Ncos(tau, n) growth table ---", flush=True)
    for tau in sorted(rows):
        seq = rows[tau]
        ns = [str(x[0]) for x in seq]
        cs = [x[1] for x in seq]
        print(f"  tau={int(tau*100):02d}%: n=[{','.join(ns)}]  Ncos=[{','.join(map(str,cs))}]", flush=True)
        # crude growth diagnosis
        if len(cs) >= 2:
            ratio = cs[-1] / max(cs[0], 1)
            nrat = seq[-1][0] / seq[0][0]
            print(f"            Ncos last/first = {ratio:.2f} over n x{nrat:.0f}  "
                  f"({'GROWS with n -> SPREAD peak (slack)' if cs[-1] > cs[0]+1 else 'O(1) -> ISOLATED peak (rho->1 forced)'})", flush=True)
    print("=== done ===", flush=True)

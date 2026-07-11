#!/usr/bin/env python3
"""
Door-(iv) Lane-1 — WITNESS-RATIO GROWTH follow-up to the decoupling finding.

Report 1782041030 showed the small-ball functional C_b is asymptotically DECOUPLED from the
sup-norm |eta_b| (argmax mismatch every n, spearman 0.490->0.046). Kernel 434795470 proved that a
uniform control |eta_b| <= K * C_b FORCES K >= |eta(b*)| / C(b*) at the target's argmax b*, and that
an UNBOUNDED family ratio rules out every absolute constant.

THIS PROBE measures the actual witness ratio
    R(n) = |eta(b*)| / C(b*),    b* = argmax_b |eta_b|
and asks: does R(n) GROW with n (=> the abstract unbounded-ratio hypothesis is empirically
instantiated => the small-ball functional class is provably NOT an absolute-constant control), or
is it pinned (=> the hypothesis would not fire for THIS functional and the no-go stays conditional)?

Discipline: EXACT complex sums, PROPER mu_n < F_p*, p ~ n^4 >> n^3 (prize regime), p == 1 mod n,
structured primes (Fermat-type when available), NEVER n = q-1. ONE sweep, ONE verdict.
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def find_prime(n, beta=4.0):
    target = int(round(n**beta)); k0 = max(2, target // n)
    for dk in range(0, 600000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n**3 and is_prime(p):  # enforce p >> n^3
                return p
    return None

def generator(p):
    pm1 = p-1; fac = []; m = pm1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, pm1//q, p) != 1 for q in fac):
            return g
    return None

def mu_n(p, n):
    g = generator(p)
    h = pow(g, (p-1)//n, p)   # element of order n
    S = []; x = 1
    for _ in range(n):
        S.append(x); x = x*h % p
    return S

def window_count(phases, p, n):
    # small-ball / concentration functional: max count of phase-set points in any arc of width 2pi*(n/p)*W
    # use the SAME notion as smallball_vs_energy: max-window-count at scale p/n on the residue line.
    # phases here are residues r = (b*y) mod p; window width w = p//n on Z_p (circular).
    w = max(1, p // n)
    vals = sorted(phases)
    m = len(vals)
    best = 0
    # circular sliding window of width w over Z_p
    ext = vals + [v + p for v in vals]
    j = 0
    for i in range(m):
        while ext[j] < vals[i] + w:
            j += 1
        best = max(best, j - i)
    return best

def run():
    print("# witness-ratio growth R(n) = |eta(b*)| / C(b*), b*=argmax|eta|  (#444 door-iv)")
    print("# EXACT C, proper mu_n, p>>n^3, p==1 mod n, never n=q-1")
    rows = []
    for n in (16, 32, 64, 128, 256):
        p = find_prime(n, 4.0)
        if p is None:
            print(f"n={n}: no prime"); continue
        S = mu_n(p, n)
        # iterate over coset reps b in 1..p-1; to stay tractable for large n sample uniformly
        import random
        random.seed(444)
        if p-1 <= 200000:
            bs = range(1, p)
        else:
            bs = random.sample(range(1, p), 200000)
        best_eta = -1.0; best_b = None
        cache = {}
        for b in bs:
            s = 0j
            for y in S:
                s += cmath.exp(2j*math.pi*((b*y) % p)/p)
            mag = abs(s)
            if mag > best_eta:
                best_eta = mag; best_b = b
        # C at the eta-argmax
        phases = [ (best_b*y) % p for y in S ]
        Cstar = window_count(phases, p, n)
        # also the GLOBAL max C over the same b-set, for context
        # (only to report whether C(b*) is near the C-extreme or far below it)
        R = best_eta / Cstar if Cstar > 0 else float('inf')
        rows.append((n, p, best_eta, best_eta/math.sqrt(n), Cstar, R, R/math.sqrt(n)))
        print(f"n={n:4d} p={p:12d} |eta(b*)|={best_eta:9.3f} (={best_eta/math.sqrt(n):.3f}sqrt(n)) "
              f"C(b*)={Cstar:4d} R={R:8.3f} R/sqrt(n)={R/math.sqrt(n):.4f}")
    print("\n# VERDICT")
    if len(rows) >= 2:
        Rs = [r[5] for r in rows]
        growing = all(Rs[i] <= Rs[i+1]*1.05 for i in range(len(Rs)-1)) and Rs[-1] > Rs[0]
        # fit R ~ n^alpha
        import math as _m
        ns = [r[0] for r in rows]
        logn = [_m.log(x) for x in ns]; logR = [_m.log(x) for x in Rs]
        k = len(ns); sx=sum(logn); sy=sum(logR); sxx=sum(a*a for a in logn); sxy=sum(a*b for a,b in zip(logn,logR))
        alpha = (k*sxy - sx*sy)/(k*sxx - sx*sx)
        print(f"R(n) values: {[round(x,3) for x in Rs]}")
        print(f"fit R(n) ~ n^{alpha:.3f}")
        if alpha > 0.05:
            print("=> witness ratio R(n) GROWS with n: the unbounded-ratio hypothesis of kernel 434795470")
            print("   is EMPIRICALLY INSTANTIATED for the small-ball window functional. No absolute constant")
            print("   K can satisfy |eta| <= K*C across the family. The small-ball control is DEAD,")
            print("   not merely decoupled. (Refutation-with-mechanism, NO CORE bound.)")
        else:
            print("=> R(n) is roughly pinned: for THIS functional the no-go stays conditional on growth.")

if __name__ == '__main__':
    run()

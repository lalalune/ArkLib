#!/usr/bin/env python3
"""
Door-(iv) probe 2: ADVERSARIAL re-check of half-mass balance at the GLOBAL worst-b.

Probe 1 found worst-b is strongly balanced (r(b*) at 83-100th pct). This re-checks
with FULL F_p^* scans only (no sampling), multiple structured primes, higher precision,
and asks the sharp question: is balance FORCED toward 1 as n grows, or just biased-high?
Also reports the TOP-k worst b's balance (not just the single argmax) to rule out a
single-point fluke. NEVER n=q-1.
"""
import cmath, math
from sympy import factorint

def primitive_root(p):
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError

def subgroup_mu(p, g, n):
    h = pow(g, (p-1)//n, p)
    elts = []; x = 1
    for _ in range(n):
        elts.append(x); x = (x*h) % p
    return elts, h

def eta_halves(p, b, h_n, n):
    half = n//2
    h2 = (h_n*h_n) % p
    A = 0j; B = 0j; x = 1
    for _ in range(half):
        A += cmath.exp(2j*math.pi*(b*x % p)/p); x = (x*h2) % p
    x = h_n % p
    for _ in range(half):
        B += cmath.exp(2j*math.pi*(b*x % p)/p); x = (x*h2) % p
    return A, B

def find_prime_with_subgroup(n, beta):
    p_target = max(int(n**beta), n**3 * 4)
    base = ((p_target // n) + 1) * n + 1
    while True:
        p = base
        if p > 2 and all(p % d for d in range(3, int(p**0.5)+1, 2)):
            return p
        base += n

def run_full(n, beta, cap=200000):
    p = find_prime_with_subgroup(n, beta)
    if (p-1) > cap:
        print(f"n={n} beta={beta} p={p}: SKIP (full scan > {cap})")
        return
    g = primitive_root(p)
    mu_n, h_n = subgroup_mu(p, g, n)
    data = []  # (mag, r, b)
    for b in range(1, p):
        A, B = eta_halves(p, b, h_n, n)
        mag = abs(A+B)
        nA, nB = abs(A), abs(B)
        mx = max(nA, nB); mn = min(nA, nB)
        r = (mn/mx) if mx > 1e-12 else 1.0
        data.append((mag, r, b))
    data.sort(reverse=True)
    topk = data[:10]
    rs = sorted(x[1] for x in data)
    mean = sum(rs)/len(rs)
    print(f"n={n} beta={beta} p={p} FULL scan over {p-1} freqs.  mean balance r={mean:.4f}")
    print(f"   TOP-10 worst-b: mag, balance_r:")
    for mag, r, b in topk:
        print(f"     ‖eta‖={mag:.4f}  r={r:.4f}  b={b}")
    topk_r = [x[1] for x in topk]
    print(f"   top-10 mean r = {sum(topk_r)/len(topk_r):.4f}  (global mean {mean:.4f})  -> balance enrichment = {(sum(topk_r)/len(topk_r))/mean:.2f}x")

if __name__ == "__main__":
    print("=== ADVERSARIAL full-scan re-check: half-mass balance at worst-b ===")
    # n=16 at a couple distinct structured primes (full scan feasible)
    for n, beta in [(16,4),(16,4.3),(16,4.6)]:
        run_full(n, beta)
        print()

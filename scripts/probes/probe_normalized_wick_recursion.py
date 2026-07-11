#!/usr/bin/env python3
"""
probe_normalized_wick_recursion.py  (#444 — formalization-targeting probe for the NORMALIZED moment recursion)

Goal: confirm the EXACT integer recursion E_{r+1} = n*E_r + cross_r (proven in-tree as rEnergy_succ),
and the normalized form a_{r+1} = (a_r + 2r*c_r)/(2r+1) with
   Wick_r := (2r-1)!! * n^r ,   a_r := E_r / Wick_r ,   c_r := cross_r / (2r * n * Wick_r).
Verify ALGEBRAICALLY that a_{r+1} = (a_r + 2r c_r)/(2r+1) holds as an IDENTITY (must, by construction),
and EMPIRICALLY whether c_r <= 1 (the single open inequality) at PROPER thin mu_n, prize-regime p.

This is the ONE-SWEEP probe for the conditional-pin brick: it does NOT re-map thickness; it confirms
(a) the recursion is an exact identity (so the Lean induction is sound), and
(b) the threshold object c_r — whether the single open inequality c_r<=1 is the right wall.

THIN 2-power mu_n, PROPER (m=(p-1)/n>1, p~n^4, NEVER n=q-1), two primes per n (char-0 faithfulness).
"""
import sympy
from collections import Counter
from math import log

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def find_primes(n, beta, k=2):
    t = int(n**beta); m = max(2, t//n); out = []
    while len(out) < k:
        p = m*n + 1
        if p >= t*0.6 and sympy.isprime(p):
            out.append(p)
        m += 1
    return out

def energies(n, p, rmax):
    """Exact integer E_r = #{(v,w) in (mu_n^r)^2 : sum v = sum w} via dense convolution.
    cross_r := E_{r+1} - n*E_r (the off-diagonal autocorrelation mass)."""
    base = roots(n, p)
    h = {0: 1}                      # freq for r=0: only empty tuple, sum 0
    E = {0: sum(c*c for c in h.values())}   # E_0 = 1
    freqs = {0: dict(h)}
    for r in range(1, rmax+1):
        nh = Counter()
        for t, c in h.items():
            for x in base:
                nh[(t+x) % p] += c
        h = dict(nh)
        E[r] = sum(c*c for c in h.values())
    return E

def dfact(r):
    v = 1
    for i in range(1, r+1):
        v *= (2*i-1)
    return v

print("Normalized Wick recursion check:  E_{r+1} = n*E_r + cross_r ;  a_r=E_r/Wick_r ;  c_r=cross_r/(2r*n*Wick_r)")
print("Wick_r = (2r-1)!! * n^r.  Open inequality is c_r <= 1 (<=> cross_r <= 2r*n*Wick_r).")
print(f"{'n':>4} {'p':>11} {'r':>2} {'a_r':>8} {'c_r':>8} {'a_{r+1}':>8} {'rec_ok':>6} {'cr<=1':>6} {'ar<=1':>6}")
for n in [16, 32]:
    for p in find_primes(n, 4.0, 2):
        rstar = max(2, round(log(p)))
        rmax = min(rstar, 8 if n <= 16 else (7 if n <= 32 else 6))
        E = energies(n, p, rmax)
        for r in range(1, rmax):
            cross = E[r+1] - n*E[r]
            Wr = dfact(r) * n**r
            Wr1 = dfact(r+1) * n**(r+1)
            a_r = E[r]/Wr
            a_r1 = E[r+1]/Wr1
            c_r = cross/(2*r*n*Wr) if r >= 1 else float('nan')
            # algebraic identity check: a_{r+1} should equal (a_r + 2r c_r)/(2r+1)
            pred = (a_r + 2*r*c_r)/(2*r+1)
            rec_ok = abs(pred - a_r1) < 1e-9
            tag = "  (DC-tail r~r*)" if r >= rstar-1 else ""
            print(f"{n:>4} {p:>11} {r:>2} {a_r:>8.4f} {c_r:>8.4f} {a_r1:>8.4f} "
                  f"{str(rec_ok):>6} {str(c_r<=1.0+1e-9):>6} {str(a_r<=1.0+1e-9):>6}{tag}")
    print()

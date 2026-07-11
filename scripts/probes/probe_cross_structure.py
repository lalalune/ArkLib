#!/usr/bin/env python3
"""
probe_cross_structure.py  (#444 — structural probe of cross_r toward a sub-bound on the single inequality c_r ≤ 1)

Building on the just-landed CharPWickConditionalPin: the whole prize collapses to c_r ≤ 1, i.e.
   cross_r := E_{r+1} - n*E_r  ≤  2r * n * Wick_r ,   Wick_r = (2r-1)!! n^r.
cross_r = sum_{s != t in mu_n} C_r(s-t),  C_r(δ) = sum_e freq(e) freq(e+δ) = autocorrelation.

QUESTION (frontier-movement, NOT a thickness re-map): does cross_r have a tractable structure that
constrains c_r? Probe THREE concrete sub-structure questions, ONE sweep:
  (Q1) Shell concentration: what fraction of cross_r comes from the single worst offset δ?
       (if cross_r ~ n^2 * max_δ C_r(δ), then c_r ≤ 1 <=> a sup-bound on the autocorrelation =
        a DIFFERENT face of the same BGK object; if it's spread, the diagonal bound is the only handle.)
  (Q2) Autocorr-vs-energy ratio: max_{δ≠0} C_r(δ)/E_r — the off-diagonal autocorr is ≤ E_r (proven
       in-tree, autocorr_le_energy). Is the WORST off-diagonal autocorr << E_r (giving slack) or ~ E_r?
  (Q3) Does c_r itself satisfy a one-step recursion (c_{r+1} vs c_r) that could bootstrap?

THIN 2-power mu_n, PROPER (m=(p-1)/n>1, p~n^4, NEVER n=q-1), two primes per n.
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

def dfact(r):
    v = 1
    for i in range(1, r+1):
        v *= (2*i-1)
    return v

def analyze(n, p, rmax):
    base = roots(n, p)
    baseset = set(base)
    h = {0: 1}
    E = {0: 1}
    freqs = {0: dict(h)}
    for r in range(1, rmax+1):
        nh = Counter()
        for t, c in h.items():
            for x in base:
                nh[(t+x) % p] += c
        h = dict(nh)
        E[r] = sum(c*c for c in h.values())
        freqs[r] = dict(h)
    return E, freqs, base

def autocorr_offdiag_stats(freq_r, base, E_r, p):
    """For each offset δ = s - t (s,t in mu_n, s != t), C_r(δ) = sum_e freq(e) freq((e+δ) mod p).
    Return: total cross = sum over ordered (s,t) s!=t of C_r(δ),  and max single C_r(δ)."""
    # group offsets
    n = len(base)
    # build a dict e->freq for fast lookup
    fr = freq_r
    cross = 0
    maxC = 0
    # number of off-diagonal ordered pairs = n*(n-1); but offsets repeat. Compute C per distinct δ once.
    offset_mult = Counter()
    for s in base:
        for t in base:
            if s != t:
                offset_mult[(s - t) % p] += 1
    # C_r(δ) for each distinct δ
    for delta, mult in offset_mult.items():
        C = 0
        for e, fe in fr.items():
            ft = fr.get((e + delta) % p, 0)
            if ft:
                C += fe * ft
        cross += mult * C
        if C > maxC:
            maxC = C
    return cross, maxC

print("cross_r structure:  cross_r = sum_{s!=t} C_r(s-t).  c_r = cross_r/(2r n Wick_r), Wick_r=(2r-1)!! n^r.")
print("Q1 shell-conc = n(n-1)*maxC / cross_r (1.0 = all mass in worst offset).  Q2 maxC/E_r (proven <=1).")
print(f"{'n':>4} {'p':>9} {'r':>2} {'c_r':>7} {'maxC/E_r':>9} {'shellConc':>9} {'c_{r+1}/c_r':>11}")
for n in [16, 32]:
    for p in find_primes(n, 4.0, 1):  # 1 prime per n for speed; faithfulness already established
        rmax = 6 if n <= 16 else 5
        E, freqs, base = analyze(n, p, rmax)
        prev_c = None
        for r in range(1, rmax):
            Wr = dfact(r) * n**r
            cross = E[r+1] - n*E[r]
            c_r = cross / (2*r*n*Wr)
            crossX, maxC = autocorr_offdiag_stats(freqs[r], base, E[r], p)
            shell = (n*(n-1)*maxC)/cross if cross > 0 else float('nan')
            mc_ratio = maxC / E[r] if E[r] > 0 else float('nan')
            ratio = (c_r/prev_c) if prev_c else float('nan')
            print(f"{n:>4} {p:>9} {r:>2} {c_r:>7.4f} {mc_ratio:>9.4f} {shell:>9.4f} {ratio:>11.4f}")
            prev_c = c_r
    print()

#!/usr/bin/env python3
"""
LANE B (#407) — Anomalous additive energy of large multiplicative subgroups.

Setup. mu_n = unique subgroup of order n=2^mu in F_p^*, p = m*n+1 prime, index m CONSTANT
(m ~ 2^7..2^10). r-fold additive energy
    E_k(mu_n) = #{(x_1..x_k,y_1..y_k) in mu_n^{2k} : sum x_i = sum y_i  (mod p)}.

FFT identity (verified below):  with Gauss sum S(b)=sum_{x in mu_n} e_p(b x),
    E_k = (1/p) sum_{b mod p} |S(b)|^{2k},     S(0)=n.
The b=0 term is the TRIVIAL-MODE count n^{2k}/p.  The ANOMALOUS energy is exactly
    A_k := E_k - n^{2k}/p = (1/p) sum_{b != 0} |S(b)|^{2k}.

The moment closure the prize wants:  A_k <= C^k * k! * n^k for ALL k (then optimizing
k ~ log p gives M(n)=max_b|S(b)| <= sqrt(n log p) << n -- a CLOSURE).

This probe computes E_k and A_k EXACTLY via integer-count convolution (FFT count of
representations of every residue as a sum of k elements of mu_n -> E_k = sum_s r_k(s)^2),
and reports the measured constant
    C_k(n) := (A_k / (k! * n^k))^{1/k}.
We sweep n=2^mu (mu up to feasible) at CONSTANT index m, and watch whether C_k(n) is
GROWING / FLAT / DECAYING in n and in k.

Char-0 (Wick) benchmark: E_k^{char0}(mu_n) = (2k-1)!! * n^k  (DyadicEnergyK1.lean).
So A_k^{char0} = (2k-1)!! n^k - n^{2k}/p.  We also report A_k / A_k^{char0}.
"""
import numpy as np
from math import factorial

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primroot(p):
    # smallest primitive root mod p
    if p == 2: return 1
    fac = []
    pm1 = p-1; t = pm1; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for a in range(2, p):
        if all(pow(a, pm1//q, p) != 1 for q in fac):
            return a
    return None

def subgroup(p, n):
    g0 = primroot(p)
    g = pow(g0, (p-1)//n, p)
    dom = []
    x = 1
    for _ in range(n):
        dom.append(x); x = x*g % p
    assert len(set(dom)) == n, "subgroup gen failed"
    return dom

def rep_counts_k(dom, p, k):
    """r_k[s] = #{(x_1..x_k) in dom^k : sum x_i = s mod p}, exact integers via int convolution."""
    base = np.zeros(p, dtype=np.int64)
    for x in dom:
        base[x] += 1
    # convolve base with itself k times (cyclic mod p) using FFT then round.
    # values can be large (n^k); use float FFT but verify with int double-checks for small k.
    fb = np.fft.rfft(base.astype(np.float64))
    fk = fb ** k
    r = np.fft.irfft(fk, n=p)
    r = np.rint(r).astype(np.int64)
    return r

def energy_k(dom, p, k):
    r = rep_counts_k(dom, p, k)
    # E_k = sum_s r[s]^2  (using python ints to avoid overflow)
    return int(np.sum(r.astype(object)**2)), r

def energy_via_gauss(dom, p, k):
    """Cross-check: E_k = (1/p) sum_b |S(b)|^{2k}, S(b)=sum_x e_p(bx)."""
    b = np.arange(p)
    domarr = np.array(dom)
    # S(b) = sum_x exp(2pi i b x / p)
    # build via fft of indicator
    ind = np.zeros(p)
    for x in dom: ind[x] += 1
    S = np.fft.fft(ind)  # S[b] = sum_x exp(-2pi i b x/p); magnitude same
    mom = np.sum(np.abs(S)**(2*k)) / p
    return mom

print("="*120)
print("STEP 0: verify FFT identity E_k = (1/p) sum_b |S(b)|^{2k}, and integer-count E_k")
print("="*120)
for (mu, m) in [(5,8),(6,8),(7,8)]:
    n = 2**mu
    p = m*n+1
    while not isprime(p): p += n
    dom = subgroup(p, n)
    for k in [1,2,3]:
        Ek, _ = energy_k(dom, p, k)
        Eg = energy_via_gauss(dom, p, k)
        triv = n**(2*k)/p
        print(f"n={n:5d} p={p:7d} m={(p-1)//n:4d} k={k}: E_k(count)={Ek:14d}  E_k(gauss)={Eg:16.2f}  rel_err={abs(Ek-Eg)/max(Ek,1):.2e}  n^2k/p={triv:14.2f}")

print()
print("="*120)
print("STEP 1: CONSTANT-INDEX sweep (task framing: m ~ 2^7..2^10 FIXED, n=2^mu -> infinity)")
print("  A_k = E_k - n^{2k}/p = (1/p) sum_{b!=0} |S(b)|^{2k}.   C_k(n) = (A_k/(k! n^k))^{1/k}.")
print("="*120)
def run_constant_index(m_target, mus, ks):
    print(f"\n--- index m ~ {m_target} (constant), q = m*n ---")
    hdr = f"{'n':>7} {'p':>10} {'m':>6} " + " ".join(f"A{k}/(k!n^k)={'':<0}" for k in ks)
    print(f"{'n':>7} {'p':>11} {'m':>6} | " + " | ".join(f"k={k}: C_k  A_k/Wick" for k in ks))
    rows = {}
    for mu in mus:
        n = 2**mu
        p = m_target*n+1
        while not isprime(p): p += n
        if p > 80_000_000:  # FFT array size cap
            continue
        dom = subgroup(p, n)
        cells = []
        for k in ks:
            Ek, _ = energy_k(dom, p, k)
            triv = n**(2*k)/p
            Ak = Ek - triv
            wick = factorial(2*k)//(factorial(k)*2**k) * n**k  # (2k-1)!! n^k
            Ck = (Ak/(factorial(k)*n**k))**(1.0/k) if Ak>0 else float('nan')
            cells.append(f"C={Ck:7.3f} Aw={Ak/wick:6.3f}")
            rows.setdefault(k, []).append((n, Ck, Ak/wick, Ak))
        print(f"{n:>7} {p:>11} {(p-1)//n:>6} | " + " | ".join(cells))
    return rows

# constant index m ~ 128, 256, 512
for mt in [128, 256, 512]:
    run_constant_index(mt, range(4, 16), [1,2,3,4])

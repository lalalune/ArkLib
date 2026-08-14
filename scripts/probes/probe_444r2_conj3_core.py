#!/usr/bin/env python3
"""
probe_444r2_conj3_core.py (#444) -- ROUND 3 conjecture factory C21-C28 shared harness.

Exact integer / mod-p arithmetic. PROPER mu_n only (n | p-1, m=(p-1)/n > 1, n != q-1).
Multi-prime. RULE-3 gate: a thin (beta=4-5) mechanism must NOT also hold for a thick
negation-closed RANDOM set of the same size (thick prize-FALSE). DC-subtracted A_r.

M(n,p) = max_{b !=0 mod p} |sum_{x in mu_n} e_p(b x)|.   Prize: M <= C sqrt(n log m).
"""
import math, cmath, random
from collections import Counter

# ---------- number theory ----------
def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    i = 5
    while i*i <= x:
        if x % i == 0 or x % (i+2) == 0: return False
        i += 6
    return True

def find_prime(n, beta):
    """smallest prime p = n*m+1 with m >= n^(beta-1), i.e. p ~ n^beta, mu_n PROPER."""
    target = int(round(n ** beta))
    p = target - (target % n) + 1
    while p <= n+1 or not is_prime(p) or (p-1) % n != 0:
        p += n
    return p

def find_prime_index(n, m_min):
    """smallest prime p = n*m+1 with m >= m_min (index control)."""
    m = m_min
    while True:
        p = n*m + 1
        if is_prime(p): return p
        m += 1

def primitive_root(p):
    if p == 2: return 1
    pm = p-1; fac = []
    t = pm; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, pm//q, p) != 1 for q in fac): return g
    raise RuntimeError

def subgroup(n, p):
    """mu_n = order-n mult subgroup of F_p, as a list of residues."""
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)]

def neg_closed_random(n, p, seed=0):
    """thick RULE-3 control: a negation-closed random set of size n in F_p^* (-x for each x)."""
    rng = random.Random(seed)
    assert n % 2 == 0
    S = set();
    while len(S) < n:
        x = rng.randrange(1, p)
        if x in S or (p-x) in S: continue
        S.add(x); S.add(p-x)
    return list(S)

# ---------- Gauss-period spectrum (exact via per-b sum; no size-p FFT) ----------
def eta_b(S, b, p):
    """eta_b = sum_{x in S} e_p(b x), exact complex via roots of unity table."""
    acc = 0j
    twopi = 2*math.pi/p
    for x in S:
        ang = twopi * ((b*x) % p)
        acc += complex(math.cos(ang), math.sin(ang))
    return acc

def M_of(S, p):
    """max_{b!=0} |eta_b| and argmax b, via numpy FFT of the indicator. O(p log p)."""
    import numpy as np
    ind = np.zeros(p, dtype=float)
    for x in S: ind[int(x)] = 1.0
    spec = np.abs(np.fft.fft(ind))
    spec[0] = 0.0
    b = int(spec.argmax())
    return float(spec[b]), b

def mag2_spectrum(S, p):
    """list of |eta_b|^2 for b=0..p-1 (exact-ish float). For energies."""
    return [abs(eta_b(S, b, p))**2 for b in range(p)]

# ---------- DC-subtracted energies via integer sumset convolution (EXACT) ----------
def energies_exact(S, p, rmax):
    """E_r = sum_t count_r(t)^2 exactly; A_r = E_r - n^{2r}/p (DC-subtracted)."""
    n = len(S)
    h = Counter({0:1}); E = {0:1}
    for r in range(1, rmax+1):
        nh = Counter()
        for t,c in h.items():
            for x in S: nh[(t+x)%p] += c
        h = nh
        E[r] = sum(c*c for c in h.values())
    A = {r: E[r] - (n**(2*r))/p for r in E}
    return E, A

if __name__ == "__main__":
    # smoke test
    n, p = 16, find_prime(16, 3.0)
    S = subgroup(n, p)
    print("n=%d p=%d (beta~3) index m=%d" % (n, p, (p-1)//n))
    M, b = M_of(S, p)
    print("M=%.4f  M/sqrt(n)=%.4f  sqrt(n*log m)=%.4f" %
          (M, M/math.sqrt(n), math.sqrt(n*math.log((p-1)//n))))
    E, A = energies_exact(S, p, 4)
    print("E_r:", {r: E[r] for r in range(1,5)})
    print("A_r:", {r: round(A[r],2) for r in range(1,5)})

#!/usr/bin/env python3
"""
probe_dooriv_fulltrace_perfect_square.py  (#444, door-(iv) / variance-core extension)

CLAIM under test (frontier-movement extension of _DiffTraceDiagonalExtraction):

  The FULL (unpunctured) first moment over the difference variety is a PERFECT SQUARE MODULUS:
    FullTrace := Σ_T Σ_{T'∈Rel} Jphase(diffTuple T T')
             =  Σ_T Σ_{T'∈Rel} Jphase(T)·conj(Jphase(T'))     [pairCorr_eq_diff]
             =  (Σ_T Jphase(T)) · conj(Σ_{T'} Jphase(T'))
             =  | Σ_T Jphase(T) |^2   >= 0   (a NON-NEGATIVE REAL).

  Combined with my diagonal-extraction identity FullTrace = #Rel + DiffTrace, this gives the
  EXACT Plancherel-type two-sided floor for the variance core:
    DiffTrace.re = |Σ_T Jphase(T)|^2 - #Rel  >=  -#Rel.
  i.e. the off-diagonal first moment can DROP at most #Rel below zero — an exact, explicit,
  unconditional lower bound (NOT the open upper bound; this is the trivial/floor side).

Verified on REAL mu_n data (proper 2-power subgroup, p >> n^3, NEVER n=q-1).
"""
import math, cmath, random

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def find_prime_thin(n, beta):
    target = int(n**beta)
    p = target - (target % n) + 1
    if p <= target: p += n
    for _ in range(2000000):
        if isprime(p): return p
        p += n
    return None

def factor(x):
    fs = set(); d = 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

def generator(p):
    pm1 = p-1; fs = factor(pm1)
    for c in range(2, p):
        if all(pow(c, pm1//q, p) != 1 for q in fs): return c
    return None

def subgroup(n, p, g):
    h = pow(g, (p-1)//n, p)
    S = []; v = 1
    for _ in range(n):
        S.append(v); v = (v*h) % p
    return S

def ep(a, p):
    return cmath.exp(2j*math.pi*(a % p)/p)

def Jphase(T, p):
    prod = 1+0j; s = 0
    for x in T:
        prod *= ep(x, p); s += x
    return prod * (ep(s, p).conjugate())

def Jphase_difftuple(T, Tp, p):
    dt = list(T) + [(-x) % p for x in Tp]
    return Jphase(dt, p)

def run(n, beta, r, n_rel, seed):
    random.seed(seed)
    p = find_prime_thin(n, beta); g = generator(p); mu = subgroup(n, p, g)
    Rel = set(); tries = 0
    while len(Rel) < n_rel and tries < n_rel*50:
        Rel.add(tuple(random.choice(mu) for _ in range(r))); tries += 1
    Rel = list(Rel)
    Js = [Jphase(T, p) for T in Rel]
    # FullTrace directly on concatenated tuples
    full = sum(Jphase_difftuple(Rel[i], Rel[j], p)
               for i in range(len(Rel)) for j in range(len(Rel)))
    # the perfect-square form
    S = sum(Js)
    sq = S * S.conjugate()
    # off-diagonal
    diff = full - len(Rel)
    floor_gap = diff.real - (-len(Rel))   # should be >= 0 always (= |S|^2)
    return (p, len(Rel), full, sq, abs(full - sq), full.imag,
            diff.real, floor_gap, abs(sq.imag))

if __name__ == "__main__":
    print("# probe: FullTrace = |Σ Jphase|^2 (perfect square modulus, nonneg real)")
    print("# n,beta,r,|Rel|,p : |Full - |S|^2|, Im(Full), DiffTrace.re, DiffTrace.re+#Rel(=|S|^2>=0)")
    worst_sq = 0.0; worst_im = 0.0; min_floor = 1e18; worst_sqim = 0.0
    for n in [16, 32, 64]:
        for beta in [4.0, 4.5]:
            for r in [3, 4, 5]:
                p, nrel, full, sq, sqerr, fim, dre, fg, sqim = run(n, beta, r, 40, 2024+n+r)
                print(f"n={n:3d} beta={beta} r={r} |Rel|={nrel:3d} p={p:>12d}  "
                      f"sq_err={sqerr:.2e} Im(Full)={fim:+.2e}  Diff.re={dre:+.2f}  floor_gap={fg:+.4f}")
                worst_sq = max(worst_sq, sqerr); worst_im = max(worst_im, abs(fim))
                min_floor = min(min_floor, fg); worst_sqim = max(worst_sqim, sqim)
    print(f"\n# VERDICT worst |FullTrace - |ΣJphase|^2| = {worst_sq:.3e} (should be ~0)")
    print(f"# VERDICT worst |Im(FullTrace)|            = {worst_im:.3e} (should be ~0)")
    print(f"# VERDICT min (DiffTrace.re + #Rel) = min |S|^2 = {min_floor:.4f} (should be >= 0)")
    print("# If all hold: FullTrace = |Σ Jphase|^2 >= 0  ⟹  DiffTrace.re >= -#Rel (exact floor).")

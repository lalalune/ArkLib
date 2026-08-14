#!/usr/bin/env python3
"""
probe_dooriv_difftrace_diagonal_extraction.py  (#444, door-(iv) / variance-core extension)

CLAIM under test (frontier-movement extension of _NextDifferenceVariety / _DiffTraceReality):

  A Lang-Weil / Katz character-sum estimate counts the FULL (unpunctured) variety
    FullTrace := Σ_T Σ_{T' ∈ Rel} Jphase(diffTuple T T'),
  i.e. INCLUDING the diagonal T = T'.  The variance core needs the PUNCTURED
  off-diagonal trace
    DiffTrace := Σ_T Σ_{T' ≠ T} Jphase(diffTuple T T').
  These differ exactly by the diagonal.  Each diagonal term is
    Jphase(diffTuple T T) = Jphase(T) * conj(Jphase(T)) = |Jphase(T)|^2 = 1
  (since each Jphase is a UNIT for a unit additive character theta).  Hence the
  EXACT decomposition:
        FullTrace = #Rel + DiffTrace,   equivalently   DiffTrace = FullTrace - #Rel.

  This is the diagonal-extraction bridge: it tells the Katz/Lang-Weil consumer the
  EXPLICIT MAIN TERM (#Rel) to subtract off the full point count to recover the
  variance-core object.  Pure algebra (each Jphase a unit), but verified on REAL mu_n
  data (proper 2-power subgroup, p >> n^3, NEVER n=q-1) so the Lean formalization rests
  on a checked fact.

Jphase(theta, x) := (prod_i theta(x_i)) * conj(theta(sum_i x_i)),  theta = additive char e_p.
diffTuple(T, T') := append(T, -T')   (the 2r-tuple).
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
        if isprime(p):
            return p
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
        if all(pow(c, pm1//q, p) != 1 for q in fs):
            return c
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
    prod = 1+0j
    s = 0
    for x in T:
        prod *= ep(x, p)
        s += x
    return prod * (ep(s, p).conjugate())

def Jphase_difftuple(T, Tp, p):
    """Jphase(diffTuple T T') with diffTuple = append(T, -T'), computed DIRECTLY
    on the concatenated 2r-tuple (does not assume the pairCorr factorization)."""
    dt = list(T) + [(-x) % p for x in Tp]
    return Jphase(dt, p)

def run(n, beta, r, n_rel, seed):
    random.seed(seed)
    p = find_prime_thin(n, beta)
    g = generator(p)
    mu = subgroup(n, p, g)
    Rel = set()
    tries = 0
    while len(Rel) < n_rel and tries < n_rel*50:
        T = tuple(random.choice(mu) for _ in range(r))
        Rel.add(T)
        tries += 1
    Rel = list(Rel)
    Js = [Jphase(T, p) for T in Rel]

    full = 0+0j   # FullTrace: includes diagonal T=T'
    diff = 0+0j   # DiffTrace: off-diagonal only
    max_diag_err = 0.0     # |Jphase(diffTuple T T) - 1|
    max_directfact_err = 0.0  # |Jphase(diffTuple T T') - Jphase(T)*conj Jphase(T')|
    for i in range(len(Rel)):
        for j in range(len(Rel)):
            # compute Jphase(diffTuple) DIRECTLY on the concatenated tuple
            jd = Jphase_difftuple(Rel[i], Rel[j], p)
            full += jd
            # cross-check the factorization pairCorr_eq_diff
            fact = Js[i]*Js[j].conjugate()
            max_directfact_err = max(max_directfact_err, abs(jd - fact))
            if i == j:
                max_diag_err = max(max_diag_err, abs(jd - 1.0))
            else:
                diff += jd
    decomp_err = abs(full - (len(Rel) + diff))
    return p, len(Rel), full, diff, max_diag_err, max_directfact_err, decomp_err

if __name__ == "__main__":
    print("# probe: diagonal-extraction decomposition  FullTrace = #Rel + DiffTrace")
    print("# diagonal terms Jphase(diffTuple T T) == 1 exactly (Jphase a unit)")
    print("# n,beta,r,|Rel|,p : |diag-1|, |Jdiff - factored|, |Full-(#Rel+Diff)|")
    worst_diag = 0.0
    worst_fact = 0.0
    worst_decomp = 0.0
    for n in [16, 32, 64]:
        for beta in [4.0, 4.5]:
            for r in [3, 4, 5]:
                p, nrel, full, diff, dg, fc, dc = run(n, beta, r, n_rel=40, seed=777+n+r)
                print(f"n={n:3d} beta={beta} r={r} |Rel|={nrel:3d} p={p:>12d}  "
                      f"diag_err={dg:.2e}  fact_err={fc:.2e}  decomp_err={dc:.2e}  "
                      f"(#Rel={nrel}, Diff.re={diff.real:+.4f}, Full.re={full.real:+.4f})")
                worst_diag = max(worst_diag, dg)
                worst_fact = max(worst_fact, fc)
                worst_decomp = max(worst_decomp, dc)
    print(f"\n# VERDICT worst |Jphase(diffTuple T T) - 1| = {worst_diag:.3e} (should be ~0)")
    print(f"# VERDICT worst |Jphase(diffTuple) - Jphase(T)conj Jphase(T')| = {worst_fact:.3e} (should be ~0)")
    print(f"# VERDICT worst |FullTrace - (#Rel + DiffTrace)| = {worst_decomp:.3e} (should be ~0)")
    print("# If all ~0: FullTrace = #Rel + DiffTrace exactly; #Rel is the explicit Katz main term.")

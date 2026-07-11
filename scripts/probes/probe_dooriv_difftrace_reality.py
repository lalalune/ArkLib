#!/usr/bin/env python3
"""
probe_dooriv_difftrace_reality.py  (#444, door-(iv) / variance-core extension)

CLAIM under test (extension of _NextDifferenceVariety):
  The off-diagonal first moment over the difference variety,
    DiffTrace = Σ_T Σ_{T'≠T} Jphase(diffTuple T T'),
  is REAL — because the off-diagonal index set is symmetric under the T<->T' swap and
    pairCorr(T',T) = conj(pairCorr(T,T'))   [= Jphase(T')·conj Jphase(T)]
  so the imaginary parts cancel pairwise. Hence FirstMomentDiffCancellation (a .re bound)
  loses NOTHING vs the full complex sum.

This is a pure algebraic identity, but we verify it numerically on REAL mu_n data
(proper 2-power subgroup, p >> n^3, NEVER n=q-1) so the formalization rests on a checked fact.

Jphase(theta, x) := (prod_i theta(x_i)) * conj(theta(sum_i x_i)),  theta = additive char e_p.
Rel = a finite set of r-tuples drawn from mu_n (additive carriers); we test the identity
for the FULL double sum over a sampled Rel.
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

def run(n, beta, r, n_rel, seed):
    random.seed(seed)
    p = find_prime_thin(n, beta)
    g = generator(p)
    mu = subgroup(n, p, g)
    # build Rel: sample distinct r-tuples of additive carriers from mu_n
    Rel = set()
    tries = 0
    while len(Rel) < n_rel and tries < n_rel*50:
        T = tuple(random.choice(mu) for _ in range(r))
        Rel.add(T)
        tries += 1
    Rel = list(Rel)
    # full off-diagonal first moment via diffTuple = Jphase(T)*conj(Jphase(T'))
    total = 0+0j
    # also verify pairCorr(T',T) = conj(pairCorr(T,T')) on a few pairs
    Js = [Jphase(T, p) for T in Rel]
    max_pair_err = 0.0
    for i in range(len(Rel)):
        for j in range(len(Rel)):
            if i == j: continue
            pc = Js[i]*Js[j].conjugate()
            total += pc
            # symmetry check
            pc_swap = Js[j]*Js[i].conjugate()
            max_pair_err = max(max_pair_err, abs(pc_swap - pc.conjugate()))
    return p, len(Rel), total, max_pair_err

if __name__ == "__main__":
    print("# probe: DiffTrace (off-diagonal first moment on V_diff) is REAL")
    print("# n, beta, r, |Rel|, p, total.re, total.im, max|pc(T',T)-conj pc(T,T')|")
    worst_im = 0.0
    worst_sym = 0.0
    for n in [16, 32, 64]:
        for beta in [4.0, 4.5]:
            for r in [3, 4, 5]:
                p, nrel, total, sym = run(n, beta, r, n_rel=40, seed=12345+n+r)
                print(f"n={n:3d} beta={beta} r={r}  |Rel|={nrel:3d} p={p:>12d}  "
                      f"re={total.real:+.6f} im={total.imag:+.3e}  sym_err={sym:.2e}")
                worst_im = max(worst_im, abs(total.imag))
                worst_sym = max(worst_sym, sym)
    print(f"\n# VERDICT: worst |Im(DiffTrace)| = {worst_im:.3e} (should be ~0 = float noise)")
    print(f"# VERDICT: worst |pc(T',T) - conj pc(T,T')| = {worst_sym:.3e} (should be ~0)")
    print("# If both ~0: DiffTrace is REAL; the .re bound FirstMomentDiffCancellation is the full sum.")

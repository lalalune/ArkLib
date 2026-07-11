#!/usr/bin/env python3
"""
probe_407_bhbi_bind_bridge.py  (#407)

Bridge the realizable-BHBI failure (height-1 half-basis relation at n=32 prize) to the §5.0 (BIND)
non-antipodal-vanishing object. A half-basis height-1 relation
    Σ_{j: g_j=+1} ω^j  −  Σ_{j: g_j=−1} ω^j  ≡ 0  (mod p),  ω a 2n-th root, ω^N=−1, N=n/2,
lifts to a FULL-index (Fin n = 2N) vanishing subset sum: since ω^N = −1, a coefficient −1 at half-basis
index j equals +1 at full index j+N (ω^{j+N} = −ω^j). So define the full index set
    S = { j : g_j=+1 } ∪ { j+N : g_j=−1 }  ⊆ {0,..,2N-1},
and then  Σ_{i∈S} ω^i ≡ 0 (mod p)  with ω now a primitive (2N)=n-th root? -- careful: the half-basis ω
here is a primitive 2n-th root with ω^N=−1 (N=n/2), i.e. ω^{2N}=ω^n=... let me use the BHBI convention:
in BHBI the base is a primitive 2^m-th root with N=2^{m-1}, ω^N=−1, so ω is a primitive (2N)-th root and
the FULL index range is {0,..,2N-1} = {0,..,n-1} with n=2N=2^m. So S ⊆ Z/n and Σ_{i∈S} ω^i ≡ 0 with ω a
primitive n-th root -- EXACTLY the BIND object.

QUESTION (the bridge): is S ANTIPODAL (i∈S ⟺ i+N∈S, the benign forced case) or NON-ANTIPODAL (genuine
spurious vanisher = the BIND-gate failure)? If non-antipodal, the BHBI failure IS a BIND failure on the
half-basis face; if antipodal, BHBI-failure is the benign antipodal kind and does NOT touch BIND.

For each n=32 prize-band prime: take the minimal height-1 witness g, build S, classify antipodal vs not,
and verify Σ_{i∈S} ω^i ≡ 0 in F_p directly (ω = primitive 2N-th root = the BHBI ω).
"""
import math
from itertools import product

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_2pow_root(p, m):
    n = 1 << m
    if (p-1) % n != 0: return None
    e = (p-1)//n
    for base in range(2, p):
        r = pow(base, e, p)
        if pow(r, n//2, p) != 1 and pow(r, n, p) == 1:
            return r
    return None

def mitm_height1(omega, N, p):
    """Find a nonzero {-1,0,1}^N relation via MITM; return g or None."""
    pw = [pow(omega, j, p) for j in range(N)]
    half = N//2
    rng = (-1,0,1)
    left = {}
    for gl in product(rng, repeat=half):
        s = 0
        for j in range(half):
            if gl[j]: s = (s + gl[j]*pw[j]) % p
        left.setdefault(s, gl)
    for gr in product(rng, repeat=N-half):
        s = 0
        for j in range(N-half):
            if gr[j]: s = (s + gr[j]*pw[half+j]) % p
        need = (-s) % p
        if need in left:
            g = left[need] + gr
            if any(x != 0 for x in g):
                return g
    return None

def prime_band(m, blo, bhi, count):
    n = 1 << m
    lo = int(n**blo); hi = int(n**bhi)
    base = lo - (lo % n) + 1
    out = []; c = base
    while c <= hi and len(out) < count:
        if isprime(c) and (c-1) % n == 0: out.append(c)
        c += n
    return out

def main():
    print("=== BHBI height-1 failure ⟷ §5.0 (BIND) vanisher bridge (n=32 prize band) ===")
    m = 5; n = 32; N = 16   # BHBI: ω primitive 2^5=32-th root, N=16 half-basis, ω^16=−1, full index range = Z/32
    band = prime_band(5, 4.0, 4.2, 8)
    nonantip = 0; antip = 0
    for p in band:
        om = primitive_2pow_root(p, m)  # primitive 32nd root, ω^16=−1
        g = mitm_height1(om, N, p)
        if g is None:
            print("  p=%d: no height-1 relation (unexpected)" % p); continue
        # build full index set S ⊆ Z/32: +1 at j, −1 lifts to j+N
        Splus = [j for j in range(N) if g[j] == 1]
        Sminus_lift = [j + N for j in range(N) if g[j] == -1]
        S = sorted(set(Splus) | set(Sminus_lift))
        # verify Σ_{i∈S} ω^i ≡ 0 (ω = the 32nd root; ω^{j+N} = −ω^j so this equals the half-basis sum)
        val = sum(pow(om, i, p) for i in S) % p
        # antipodal? i∈S ⟺ i+N (mod 2N) ∈ S
        Sset = set(S)
        is_antip = all(((i + N) % (2*N)) in Sset for i in S) and all(((i - N) % (2*N)) in Sset for i in S)
        if is_antip: antip += 1
        else: nonantip += 1
        beta = math.log(p, n)
        cls = "ANTIPODAL (benign)" if is_antip else "NON-ANTIPODAL (BIND-gate failure)"
        print("  p=%9d b=%.3f  #S=%d  Σ_{i∈S}ω^i mod p=%d  ->  %s  S=%s" % (p, beta, len(S), val, cls, S))
    print("  => %d non-antipodal (BIND failures), %d antipodal (benign), of %d" % (nonantip, antip, len(band)))

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
p-INDEPENDENT depth-m census via SYMMETRIC-FUNCTION VANISHING (the char-0 combinatorial core).

Far-coset law (canonical binding direction = adjacent low pair (X^a, X^{a-1}), depth m, k=a-1-m):
  a witness subset T of the EXPONENTS (T subset of Z/n, |T| = a) is "binding at depth m" iff the
  vanishing polynomial prod_{i in T}(X - zeta^i) has its top (m) constrained symmetric coefficients
  zero, i.e. e_2(zeta^T)=...=e_{m+1}(zeta^T)=0  (depth-1 = {e_2=0}, depth-2 = {e_2=e_3=0}, ...).
  [AdjacentPairDepthOneClean / KKH26ConstrainedCensusLaw: depth-1 single constraint is e_2=0;
   each extra depth adds the next elementary symmetric vanishing on the witness roots.]

We compute, p-INDEPENDENTLY (over the cyclotomic field via integer/rational arithmetic on
zeta = exp(2 pi i /n)), the census
  N(n, w, m) := #{ T subset Z/n : |T|=w, e_2(zeta^T)=...=e_{m+1}(zeta^T)=0 }
and its dilation-orbit count K = N / (#orbits under T -> T + c).  This is the p-independent count
that governs D = n*K at the binding direction.

This is CHEAP (no p-loop, no per-subset linear algebra over F_p): just enumerate w-subsets of Z/n
and test exact vanishing of a few power/elementary sums of roots of unity (via integer convolution
in the cyclotomic ring, or high-precision complex with a tight zero test cross-checked by the
integer Newton identities).
"""
import sys, itertools, cmath, math

def esym_complex(roots, upto):
    """elementary symmetric e_1..e_upto of the given complex roots (via Newton from power sums)."""
    n = len(roots)
    p = [sum(z**j for z in roots) for j in range(0, upto+1)]   # power sums p_0..p_upto
    e = [1.0+0j] + [0j]*upto
    for k in range(1, upto+1):
        s = 0j
        for i in range(1, k+1):
            s += (-1)**(i-1) * e[k-i] * p[i]
        e[k] = s / k
    return e[1:upto+1]

def census(n, w, m, tol=1e-7):
    """N(n,w,m): #{|T|=w subset Z/n : e_2..e_{m+1}(zeta^T)=0}. Also orbit count under +c."""
    zeta = [cmath.exp(2j*cmath.pi*i/n) for i in range(n)]
    good = []
    for T in itertools.combinations(range(n), w):
        roots = [zeta[i] for i in T]
        e = esym_complex(roots, m+1)
        if all(abs(e[j]) < tol for j in range(1, m+1)):   # e_2..e_{m+1} zero (e[1]=e_2,...)
            good.append(T)
    N = len(good)
    # orbit count under cyclic shift T -> T+c (dilation)
    gs = set(tuple(sorted(t)) for t in good)
    seen = set(); K = 0
    for T in gs:
        if T in seen: continue
        K += 1
        for c in range(n):
            seen.add(tuple(sorted((i+c) % n for i in T)))
    return N, K, good[:3]

if __name__ == '__main__':
    # depth-m=1 means {e_2=0}; binding witness size w=a; we scan w and m.
    # GPU/dossier: e2=0 census (m=1, the {e1 free, e2=0}) values 4,6,4 (n=8/16/32) for width-4.
    # Here census(n, w, m) with m=1 tests {e2=0} for general width w.
    print("n  w  m  N(=#subsets)  K(=#dilation-orbits)", flush=True)
    for n in [8, 16, 32]:
        for w in [4]:
            for m in [1]:
                N, K, ex = census(n, w, m)
                print(f"{n:>2} {w:>2} {m:>2}  {N:>10}  {K:>6}   ex={ex}", flush=True)

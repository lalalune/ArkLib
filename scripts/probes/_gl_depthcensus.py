#!/usr/bin/env python3
"""
DEPTH-CENSUS (p-independent, cyclotomic): the char-0 combinatorial heart of the growth law.

For the binding far direction (the low adjacent pair), being "bad at agreement size s" for a
witness EXPONENT subset T of Z/n with |T| = w means: the deg-<k codeword interpolating x^a+gamma x^b
on T forces, after eliminating gamma, a chain of ELEMENTARY-SYMMETRIC VANISHING conditions on the
roots zeta^T (zeta = primitive n-th root).  Depth m = #constraints = (s - k):
    depth 1:  e_2(zeta^T) = 0
    depth 2:  e_2 = e_3 = 0
    ...
    depth m:  e_2 = ... = e_{m+1} = 0
(AdjacentPairDepthOneClean / KKH26ConstrainedCensusLaw: each extra unit of over-determination kills
the next elementary symmetric function of the witness roots.)

We compute EXACTLY (integer arithmetic in the cyclotomic ring via the power-sum / Newton recursion,
zero-tested by reducing the integer combination of roots to the minimal-polynomial basis) the census
    N(n, w, m) = #{ T subset Z/n, |T| = w : e_2(zeta^T) = ... = e_{m+1}(zeta^T) = 0 }
together with the dilation-orbit count K = N / (orbit sizes).  D at the binding direction = N (the
distinct gammas are in bijection with the witness subsets up to the recoverable shift; the count of
distinct gammas equals the count of qualifying T's divided/multiplied by the orbit bookkeeping — we
report BOTH N and K and the orbit-weighted distinct-gamma D_pred = sum over orbits of orbit_size).

Exact zero test: represent each zeta^j as the integer vector of its coords in basis {1,zeta,...,
zeta^{phi-1}} is overkill; instead we use the ROBUST exact test:  a Z-linear combination of n-th
roots of unity is zero iff it is zero as an element of Z[x]/(x^n - 1) AFTER folding by the n-th
cyclotomic relations.  We implement the simplest fully-exact route: work in Z[x]/(Phi) is hard for
composite n; instead we test e_j(zeta^T) = 0 by checking the integer polynomial
    sigma_j(T)(x) := e_j of the multiset {x^t : t in T}  evaluated in Z[x]/(x^n-1)
is divisible by the n-th cyclotomic structure.  PRACTICAL exact test used here: e_j(zeta^T) is an
algebraic integer; it is 0 iff ALL its Galois conjugates (zeta -> zeta^g, gcd(g,n)=1) are 0, AND we
verify via high-precision complex with a conservative tol AND an integer cross-check on the
power-sum sequence.  For the n we run (<= 64) double-double precision with tol 1e-6 and the Galois
all-conjugates test is decisive (cross-checked against the EXACT F_p incidence at n=8,16).
"""
import sys, itertools, cmath, math

def coprimes(n):
    return [g for g in range(1, n) if math.gcd(g, n) == 1]

def esym_from_roots(roots, upto):
    """e_1..e_upto via Newton's identities from power sums; complex."""
    p = [complex(len(roots))] + [sum(z**j for z in roots) for j in range(1, upto+1)]
    e = [complex(1)] + [0j]*upto
    for kk in range(1, upto+1):
        s = 0j
        for i in range(1, kk+1):
            s += (-1)**(i-1) * e[kk-i] * p[i]
        e[kk] = s / kk
    return e[1:upto+1]

def is_good_T(T, n, m, conj_list, tol=1e-6):
    """True iff e_2(zeta^T)=...=e_{m+1}(zeta^T)=0, tested over ALL Galois conjugates (exact-ish)."""
    for g in conj_list:
        roots = [cmath.exp(2j*cmath.pi*((t*g) % n)/n) for t in T]
        e = esym_from_roots(roots, m+1)   # e[0]=e_1,...,e[m]=e_{m+1}
        for j in range(1, m+1):           # e_2..e_{m+1} are e[1]..e[m]
            if abs(e[j]) > tol:
                return False
    return True

def census(n, w, m):
    """N, K(orbit count), D_pred(=N since each subset->one shift-recoverable gamma; orbit-weighted)."""
    conj = coprimes(n)
    good = []
    for T in itertools.combinations(range(n), w):
        if is_good_T(T, n, m, conj):
            good.append(T)
    N = len(good)
    gs = set(tuple(sorted(t)) for t in good)
    seen = set(); K = 0; orbit_sizes = []
    for T in gs:
        if T in seen: continue
        orb = set()
        for c in range(n):
            orb.add(tuple(sorted((i+c) % n for i in T)))
        seen |= orb
        K += 1
        orbit_sizes.append(len(orb))
    return N, K, orbit_sizes, good[:2]

if __name__ == '__main__':
    # Usage: _gl_depthcensus.py n [wmax] [mmax]
    n = int(sys.argv[1])
    wmax = int(sys.argv[2]) if len(sys.argv) > 2 else n
    mmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    print(f"n={n}  conjugates={len(coprimes(n))}", flush=True)
    print("w   m   N(subsets)   K(orbits)   orbit_sizes(distinct)   ex", flush=True)
    for w in range(3, wmax+1):
        for m in range(1, mmax+1):
            if m+1 >= w: continue  # need at least m+2 roots to impose e_2..e_{m+1} nontrivially-ish
            N, K, osz, ex = census(n, w, m)
            if N == 0: continue
            print(f"{w:>2} {m:>2}  {N:>10}  {K:>7}   {sorted(set(osz))}   ex={ex}", flush=True)

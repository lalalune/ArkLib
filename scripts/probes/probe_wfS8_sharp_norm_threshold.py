#!/usr/bin/env python3
# wf-S8 THRESHOLD-PUSH: sharp max |N_{Q(zeta_n)/Q}(sigma_T)| over bounded-weight, antipodal-free
# configs, vs the crude house bound w^{n/2} (w=2r). Reads off how far the no-spurious threshold rises.
#
# n=2^mu, phi(n)=n/2, Phi_n=x^{n/2}+1. A config reduces mod Phi_n to c in {-1,0,+1}^{n/2}, weight w=#supp.
#   N_T = prod_{j odd, 0<j<n} sigma_T(zeta^j) = prod over the phi(n) primitive roots, a NONNEG INTEGER.
#   (conjugate pairs => N = prod_{pairs} |sigma(zeta^j)|^2 >= 0.)
# Transfer (no spurious vanishing mod p) for ALL weight<=w configs iff p > Nmax(n,w) = max N_T.
# CRUDE house bound: |sigma(zeta^j)| <= w each, phi(n) factors => N_T <= w^{n/2}.
#
# Exact computation: high-precision (mpmath) product over primitive roots, round to nearest int.
# Enumeration: exhaustive over support+signs for small (n,w); for larger n use the fact that |N| is
# invariant under (rotation zeta->zeta^k for k odd) and (global sign), and the max is attained by a
# CONTIGUOUS block of +1's (or block with structure) -- we exhaustively confirm on small n then use the
# block family + random search to certify the max on larger n.

import mpmath as mp
from itertools import combinations, product
import math, sys, random

mp.mp.dps = 60  # decimal digits; norms here are < 10^40, safe

def conj_roots(n):
    # primitive n-th roots: zeta^j, j odd in [1,n)
    return [mp.e**(2j*mp.pi*mp.mpf(j)/n) for j in range(1, n, 2)]

def norm_from_coeffs(coeffs, roots, half):
    # coeffs[k] = coeff of x^k, k in [0,half); sigma(r) = sum coeffs[k]*r^k
    prod = mp.mpf(1)
    for r in roots:
        s = mp.mpc(0)
        rp = mp.mpc(1)
        for k in range(half):
            if coeffs[k]:
                s += coeffs[k]*rp
            rp *= r
        prod *= s
    # prod is real (conjugate-closed); round to int
    val = mp.re(prod)
    return round(float(val)) if abs(val) < 1e15 else int(mp.nint(val))

def exhaustive_max(n, w):
    half = n//2
    roots = conj_roots(n)
    best = 0; wit=None; cnt=0
    for ww in range(1, w+1):
        for supp in combinations(range(half), ww):
            for sg in product([-1,1], repeat=ww):
                coeffs=[0]*half
                for k,s in zip(supp,sg): coeffs[k]=s
                N = norm_from_coeffs(coeffs, roots, half)
                cnt+=1
                if N>best:
                    best=N; wit=(ww,supp,sg)
    return best, wit, cnt

def block_max(n, w):
    # candidate worst configs: contiguous block of +1 of length w (and a few structured ones)
    half=n//2; roots=conj_roots(n)
    best=0; wit=None
    cands=[]
    # contiguous all-+1 block
    cands.append([1]*w+[0]*(half-w))
    # alternating signs block
    cands.append([(-1)**k for k in range(w)]+[0]*(half-w))
    # spread (every other slot) +1
    spread=[0]*half
    for i in range(w):
        if 2*i<half: spread[2*i]=1
    cands.append(spread)
    for c in cands:
        if sum(abs(v) for v in c)>w: continue
        N=norm_from_coeffs(c,roots,half)
        if N>best: best=N; wit=tuple(c[:w])
    # random antipodal-free (within reduced coords any {-1,0,1}^half with weight w is fine)
    rng=random.Random(12345)
    for _ in range(4000):
        supp=rng.sample(range(half),w)
        c=[0]*half
        for k in supp: c[k]=rng.choice([-1,1])
        N=norm_from_coeffs(c,roots,half)
        if N>best: best=N; wit=('rand',tuple(sorted(supp)))
    return best,wit

def report(n, w, exact):
    half=n//2
    if exact:
        Nmax,wit,cnt = exhaustive_max(n,w)
        mode=f"EXACT(exhaustive, {cnt} configs)"
    else:
        Nmax,wit = block_max(n,w)
        mode="LOWER-BOUND(block+random search; certifies Nmax >= this)"
    crude = w**half
    lN = math.log(Nmax) if Nmax>0 else 0.0
    lC = half*math.log(w)
    base = Nmax**(1.0/half) if Nmax>0 else 0.0
    print(f"== n={n} phi={half}  w(=2r)={w} (r={w//2})  [{mode}] ==")
    print(f"   SHARP Nmax = {Nmax}   log={lN:.3f}  per-conj base=Nmax^(1/phi)={base:.4f}   witness={wit}")
    print(f"   CRUDE w^phi = {crude}   log={lC:.3f}  crude base=w={w}   (sqrt(w)={math.sqrt(w):.3f})")
    if Nmax>0:
        print(f"   crude/sharp log-ratio = {lC/lN:.3f}x   sharp exponent budget = {lN/lC:.3f} of crude")
    sys.stdout.flush()
    return Nmax, lN, half, base

if __name__=="__main__":
    print("# wf-S8 sharp cyclotomic-norm threshold (exact mpmath conjugate products)\n")
    rows=[]
    # exhaustive small to learn the worst family
    for n,w in [(8,4),(16,4),(8,6),(16,6)]:
        rows.append((n,w,*report(n,w,exact=True))); print()
    # larger n: certified lower bound on Nmax via structured + random search
    for n,w in [(32,4),(64,4),(128,4),(32,6),(64,6)]:
        rows.append((n,w,*report(n,w,exact=False))); print()
    print("# per-conjugate base trend (Nmax^(1/phi)) at fixed w -- does it stabilize below w?")
    for n,w,Nmax,lN,half,base in rows:
        print(f"  n={n:4d} w={w} phi={half:3d}  base={base:.4f}  (vs crude {w}, vs sqrt(w) {math.sqrt(w):.3f})")

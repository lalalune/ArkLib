#!/usr/bin/env python3
"""(BIND) — correct direction. Gate needs |N(beta)| < p (UPPER bound) to force N=0=>antipodal.
House gives |N| <= (#S)^phi(n) which is too weak at binding size #S~n/4.
PROBE: the MAX |N(beta)| over reduced coeff vectors c in {-1,0,1}^m (m=n/2), vs the house (#S)^m.
Also track at fixed weight w (=#nonzero reduced coeffs ~ relates to #S). The 'realized house slack'
log2 house - log2 maxN tells us how structurally loose the house is. If max realized log2|N|
grows MUCH slower than the house's (n/2)log2(#S), a structure-aware upper bound can re-close BIND.
KEY prize numbers: at n=128, phi=64, p~2^136. House(56) = 56^64 ~ 2^372. Realized ~2^131.
"""
import mpmath as mp
import math, itertools, random
mp.mp.dps = 50

def roots_xm1(m):
    return [mp.e**(1j*mp.pi*(2*k+1)/m) for k in range(m)]

def normN(roots, c, m):
    P = mp.mpc(1)
    for w in roots:
        val = mp.mpc(0); wp = mp.mpc(1)
        for j in range(m):
            if c[j]:
                val += c[j]*wp
            wp *= w
        P *= val
    return abs(P)

for n in [8, 16, 32, 64]:
    m = n//2
    roots = roots_xm1(m)
    logp = 4.5*math.log2(n)
    print(f"\n=== n={n} m={m} phi={m}  prize log2 p ~ {logp:.1f} bits ===", flush=True)
    # track max |N| at each weight w, and the house (w)^m for comparison (weight ~ |c|_0, an under-count of #S but a proxy)
    maxN = {}
    if m <= 8:
        for c in itertools.product([-1,0,1], repeat=m):
            if not any(c): continue
            w = sum(1 for v in c if v)
            Ni = normN(roots, c, m)
            l2 = float(mp.log(Ni)/mp.log(2)) if Ni > 0.5 else -99
            if w not in maxN or l2 > maxN[w]:
                maxN[w] = l2
    else:
        random.seed(1)
        N_samp = 6000 if m <= 16 else 2500
        for _ in range(N_samp):
            c = [random.randint(-1,1) for _ in range(m)]
            if not any(c): continue
            w = sum(1 for v in c if v)
            Ni = normN(roots, c, m)
            l2 = float(mp.log(Ni)/mp.log(2)) if Ni > 0.5 else -99
            if w not in maxN or l2 > maxN[w]:
                maxN[w] = l2
    print(f"{'w':>4} {'log2 maxN':>10} {'log2 house=w^m':>14} {'house slack':>11}", flush=True)
    overall = -99; ow = None
    for w in sorted(maxN):
        l2 = maxN[w]
        house = m*math.log2(w) if w > 0 else 0
        slack = house - l2
        if l2 > overall:
            overall = l2; ow = w
        print(f"{w:>4} {l2:>10.2f} {house:>14.2f} {slack:>11.2f}", flush=True)
    print(f"OVERALL max realized log2|N| = {overall:.2f} at weight {ow};  vs prize log2 p = {logp:.1f}", flush=True)
    print(f"  -> realized max |N| {'<' if overall < logp else '>='} p  (need < p for BIND to hold by upper bound)", flush=True)
    # growth law fit: realized max log2|N| vs n

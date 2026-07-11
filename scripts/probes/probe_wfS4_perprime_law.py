#!/usr/bin/env python3
# wf-S4 (part 3): the PER-PRIME LAW. Establish, exactly, the relation
#       Total_spur(n,p,w) = (n/2) * c_perprime(n,p,w)   [Galois simple-transitivity, EXACT]
# and measure how the per-prime concentration c_perprime grows, at the WORST (most structured)
# prime in each band, and at increasing beta. v_P-multiplicity is pinned (=1, part 2).
#
# Interpretation for the prize: M(n) = max_b |eta_b| is the HOUSE of the algebraic integer eta.
# A prime P_i "sees" a spurious config T iff sigma_T in P_i; the number of short relations a single
# prime sees = c_perprime is the per-prime concentration. The prize-relevant statement is that the
# spurious mass is SPREAD over the n/2 primes; the Galois law forces the spread to be EXACTLY n/2
# (every full orbit = one config per prime). So:
#    per-prime concentration c_perprime = (Total spur) / (n/2)   exactly when all orbits are full.
# If c_perprime grows only sub-linearly in (Total spur), the n/2 spread is doing real work.
#
# We measure: (i) is EVERY orbit full size n/2 (=> exact (n/2)x spread)? (ii) c_perprime vs n.

import itertools, math
from sympy import isprime, primitive_root

def hroot(n, p):
    g = primitive_root(p); return pow(g, (p-1)//n, p)

def total_spur_and_orbits(n, p, wmax):
    """Count ALL antipodal-free genuine char-p configs (weight<=wmax) landing in ANY prime,
    and their Galois orbit sizes. Returns (total_in_any_prime, per_prime_count_P1, orbit_sizes)."""
    half = n//2
    odd_i = [i for i in range(1, n) if i % 2 == 1]
    h = hroot(n, p)
    hpow = [pow(h, s % n, p) for s in range(half)]  # h^s for s in [0,half)
    in_any = set()
    in_P1 = []
    # enumerate signed configs choice[s] in {0,+1,-1}, weight<=wmax, fix global sign by first nonzero=+1
    for choice in itertools.product((0,1,-1), repeat=half):
        w = sum(1 for c in choice if c!=0)
        if w==0 or w>wmax: continue
        # fix global negation
        fnz = next(c for c in choice if c!=0)
        if fnz != 1: continue
        # genuine char-p (not vanishing in C)
        tot = 0j
        for s,c in enumerate(choice):
            if c: tot += c*complex(math.cos(2*math.pi*s/n), math.sin(2*math.pi*s/n))
        if abs(tot) < 1e-9: continue
        # which primes (embeddings i odd) does it vanish under?
        lands = []
        for i in odd_i:
            val = 0
            for s,c in enumerate(choice):
                if c: val = (val + c*pow(h, (i*s)%n, p)) % p
            if val == 0: lands.append(i)
        if lands:
            in_any.add(choice)
            if 1 in lands: in_P1.append(choice)
    # orbit sizes (within in_any)
    def gimg(choice, a):
        out=[0]*half
        for s,c in enumerate(choice):
            if c==0: continue
            t=(a*s)%n; sgn=c
            if t>=half: t-=half; sgn=-sgn
            out[t]=out[t]+sgn
        # re-fix global sign
        fnz=0
        for x in out:
            if x!=0: fnz=x; break
        if fnz==-1: out=[-x for x in out]
        return tuple(out)
    seen=set(); sizes=[]
    for c in in_any:
        if c in seen: continue
        orb=set([c])
        for a in odd_i:
            img=gimg(c,a)
            if img in in_any: orb.add(img)
        for x in orb: seen.add(x)
        sizes.append(len(orb))
    return len(in_any), len(in_P1), sizes

def worst_prime(n, lo, tries, wmax):
    """find the prime in band [lo, ...] with the MOST total spurious configs (weight<=wmax)."""
    best=None; m=lo//n; checked=0
    while checked<tries:
        p=n*m+1; m+=1
        if p<=lo or not isprime(p): continue
        checked+=1
        tot,_,_ = total_spur_and_orbits(n,p,wmax)
        if best is None or tot>best[1]:
            best=(p,tot)
    return best

print("wf-S4 part3: the EXACT per-prime law  Total_spur = (n/2) * c_perprime, orbits all full?")
print("at the WORST (most structured) prime per band.\n")
for n in [8, 16]:
    half=n//2; wmax=min(half,5)
    p, _ = worst_prime(n, n*n, 40, wmax)
    beta=math.log(p)/math.log(n)
    tot, cP1, sizes = total_spur_and_orbits(n, p, wmax)
    full = all(s==half for s in sizes)
    ratio = tot/cP1 if cP1 else 0
    print(f"n={n} worst p={p} beta={beta:.2f} wmax={wmax}:")
    print(f"   total spur (any prime) = {tot}")
    print(f"   per-prime count c(P1)  = {cP1}")
    print(f"   ratio total/c(P1)      = {ratio:.2f}  (n/2={half} => exact (n/2)x spread iff =n/2)")
    print(f"   orbit sizes            = {sorted(set(sizes))}  all full(={half})? {full}")
    print()

# beta sweep at n=16: per-prime concentration vs beta (does higher prize-like beta change it?)
print("beta sweep at n=16 (worst prime in each band lo=n^beta):")
n=16; half=8; wmax=4
for tgt_beta in [2.0, 3.0, 4.0]:
    lo=int(n**tgt_beta)
    p,_=worst_prime(n, lo, 60, wmax)
    tot,cP1,sizes=total_spur_and_orbits(n,p,wmax)
    beta=math.log(p)/math.log(n)
    full=all(s==half for s in sizes) if sizes else True
    print(f"   beta~{tgt_beta}: p={p} (actual beta={beta:.2f})  total={tot}  c(P1)={cP1}  "
          f"orbits full? {full}")

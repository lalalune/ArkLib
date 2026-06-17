#!/usr/bin/env python3
# wf-S4 (part 2): GROWTH of the per-prime spurious config count = #Galois orbits, and the
# Stickelberger MULTIPLICITY (valuation) pin.
#
# Part 1 established (EXACT, n=16): the spurious configs are PERFECTLY Galois-spread:
#   per-prime count c_1(w) = #(full-size n/2 Galois orbits) ; Total spur(w) = (n/2) * c_1(w).
# So the SPREAD factor is exactly n/2 (forced by Galois simple-transitivity on the n/2 primes),
# and the CONCENTRATION is c_1(w) = #orbits.
#
# DECISIVE: does the per-prime count c_1(w) (= #orbits) at FIXED bounded weight w grow with n,
# or stay bounded? If c_1 = O(1) per prime, the spurious mass is genuinely thin per-prime
# (CONCENTRATION-REDUCED, prize-favorable: each prime ideal sees few vanishing configs, so the
# Gauss period eta_b -- whose size is controlled by how many short relations vanish mod that prime
# -- cannot inflate). If c_1 grows poly(n), the per-prime concentration is real (OBSTRUCTION).
#
# M3 MULTIPLICITY: for a spurious config T with sigma_T in P_i, what is the P_i-adic valuation
# v_{P_i}(sigma_T)? Stickelberger constrains the GLOBAL factorization. We measure whether
# vanishing is always SIMPLE (v=1: sigma_T(h^i) = 0 mod p but != 0 mod p^2) -- if so, a config
# cannot contribute "depth" beyond 1 at any single prime, capping the deep-moment inflation
# per-prime even though many configs vanish.
#
# We FIX a small weight w and a structured prime per n, count orbits, and check multiplicities.

import itertools, math
from sympy import isprime, primitive_root

def musub(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return h

def find_structured_prime(n, lo, tries):
    # a "structured" prime = one admitting many short spurious relations. Pick the prime in the band
    # with the MOST weight-<=4 spurious configs (mimics Fermat-like structure at small scale).
    half = n//2
    odd_i = [i for i in range(1, n) if i % 2 == 1]
    best = None
    m = lo // n
    checked = 0
    while checked < tries:
        p = n*m+1; m += 1
        if p <= lo or not isprime(p): continue
        checked += 1
        h = musub(n, p)
        cnt = 0
        # count weight<=4 configs vanishing under embedding i=1 (one prime)
        for combo in itertools.combinations(range(half), 4):
            # try all sign patterns (2^4) but skip all-same? we want genuine
            for signs in itertools.product((1,-1), repeat=4):
                val = sum(signs[t]*pow(h, combo[t] % n, p) for t in range(4)) % p
                if val == 0:
                    cnt += 1
        if best is None or cnt > best[1]:
            best = (p, cnt)
    return best

def count_orbits_and_mult(n, p, w):
    half = n//2
    odd_i = [i for i in range(1, n) if i % 2 == 1]
    h = musub(n, p)
    # enumerate weight-exactly-w antipodal-free signed configs; find those in P_1 (embedding i=1)
    in_P1 = []
    mults = []
    p2 = p*p
    for combo in itertools.combinations(range(half), w):
        for signs in itertools.product((1,-1), repeat=w):
            # canonicalize sign (fix first sign +1 to dedupe global negation which is same config up to -1)
            if signs[0] != 1: continue
            choice = [0]*half
            for t in range(w): choice[combo[t]] = signs[t]
            choice = tuple(choice)
            val = sum(signs[t]*pow(h, combo[t] % n, p) for t in range(w)) % p
            if val == 0:
                # genuine char-p? not vanishing in C
                tot = sum(signs[t]*complex(math.cos(2*math.pi*combo[t]/n), math.sin(2*math.pi*combo[t]/n)) for t in range(w))
                if abs(tot) < 1e-9: continue
                in_P1.append(choice)
                # multiplicity mod p^2 (Hensel/valuation proxy): evaluate the SAME signed sum with
                # h lifted to a root mod p^2 (Teichmuller-ish). Approximate: use h itself; if sum%p==0,
                # check sum%p2. v=1 if sum%p2 != 0.
                val2 = sum(signs[t]*pow(h, combo[t] % n, p2) for t in range(w)) % p2
                mults.append(2 if val2 == 0 else 1)
    # group in_P1 into Galois orbits to confirm one-per-prime
    def gimg(choice, a):
        out=[0]*half
        for s,c in enumerate(choice):
            if c==0: continue
            t=(a*s)%n; sgn=c
            if t>=half: t-=half; sgn=-sgn
            out[t]=out[t]+sgn
        return tuple(out)
    cp_set=set(in_P1); seen=set(); orbits=0
    for c in in_P1:
        if c in seen: continue
        orbits+=1
        for a in odd_i:
            img=gimg(c,a)
            if img in cp_set: seen.add(img)
        seen.add(c)
    return len(in_P1), orbits, mults

print("wf-S4 part2: per-prime spurious count growth + Stickelberger multiplicity (v_P)")
print("at the most-structured prime in each band; FIXED weight w.\n")
for n in [8, 16, 32]:
    half = n//2
    sp = find_structured_prime(n, n*n, 60)
    if sp is None:
        print(f"n={n}: no prime found"); continue
    p, _ = sp
    beta = math.log(p)/math.log(n)
    print(f"n={n}  structured p={p}  beta={beta:.2f}  (n/2={half} primes)")
    for w in range(2, min(half, 6)+1):
        cnt, orbits, mults = count_orbits_and_mult(n, p, w)
        maxmult = max(mults) if mults else 0
        nmult2 = sum(1 for m in mults if m == 2)
        print(f"   w={w}: configs-in-P1={cnt:5d}  orbits={orbits:4d}  "
              f"(=per-prime concentration; total spur={cnt}*?  spread={half}x)  "
              f"maxV_P={maxmult} (#v>=2: {nmult2})")
    print()

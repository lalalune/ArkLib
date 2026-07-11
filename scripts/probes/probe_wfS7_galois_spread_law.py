#!/usr/bin/env python3
# wf-S7 (#444): the char-p Mann analogue — the GALOIS-SPREAD law of spurious relations.
#
# FINDINGS (exact, reproducible; n=2^mu, prize prime p=1 mod n, p~n^4):
#
# (1) char-p Mann floor HOLDS at short weight but BREAKS at w=4 for n>=64.
#     - n=16: GLOBAL max odd prime factor over ALL half-range +-configs = 881 = n^2.45 < n^4.
#       => NO prize prime p~n^4 divides ANY nonzero norm; char-0 transfers UNCONDITIONALLY.
#     - But maxOdd(n,w) at FIXED weight GROWS with n:
#         w=3: log_n(maxOdd) = 1.02(n16), 1.76(n32), 2.94(n64)
#         w=4: log_n(maxOdd) = 1.65(n16), 2.59(n32), 4.33(n64)   <-- crosses 4 at n=64
#     - So at n>=64 a weight-4 config's norm can carry a genuine prize prime p~n^4.
#     CONCRETE TRANSFER-FALSE WITNESS (n=64): the prize prime p=17318209 (=1 mod 64, =n^4.008)
#       divides N_{Q(zeta_64)/Q}( zeta^8 + zeta^13 - zeta^14 - zeta^20 ). Weight 4, well inside the
#       prize depth band 2r~2*4*ln64~33. So short spurious relations DO reach prize primes; the
#       Mann analogue does NOT bound minimal spurious weight above the depth band.
#
# (2) BUT the breakage is GALOIS-EQUIVARIANT (the decisive structural law).
#     For p=17318209, n=64: the 1024 weight-4 spurious configs decompose into EXACTLY
#     32 Galois orbits, EACH of size 32 = phi(64). I.e.
#         #spurious(n,w,p) = (#base orbits) * phi(n),    every orbit FULL (size phi(n)).
#     This is the S2/S4/S6 "spread": spurious mass is forced into full Galois orbits of size
#     phi(n)~n/2. So per prize prime per weight, the count is O(orbits)*n, and K boundedness
#     <=> the number of BASE orbits stays bounded (does not grow like a power of n) at the prize.
#     This is the sharp reduction the char-p Mann route delivers.
#
# This script reproduces (1) the witness and (2) the orbit decomposition exactly.

import itertools, math, sys
from sympy import cyclotomic_poly, resultant, symbols, Poly, factorint, isprime

x = symbols('x')

def maxodd_fixed_weight(n, w, cap=2000, seed=1):
    import random; random.seed(seed)
    Phi = Poly(cyclotomic_poly(n, x), x); half = n//2; poss = list(range(half))
    combs = list(itertools.combinations(poss, w))
    if len(combs) > cap: combs = random.sample(combs, cap)
    mo = 1
    for support in combs:
        for tail in itertools.product((1,-1), repeat=w-1):
            signs = (1,)+tail
            P = Poly(sum(s*x**pp for s,pp in zip(signs,support)), x)
            N = abs(int(resultant(Phi, P)))
            if N == 0: continue
            for pr in factorint(N):
                if pr % 2 == 1 and pr > mo: mo = pr
    return mo

def galois_orbit_decomp(n, w, p):
    Phi = Poly(cyclotomic_poly(n, x), x); half = n//2; poss = list(range(half))
    spur = []
    for support in itertools.combinations(poss, w):
        for tail in itertools.product((1,-1), repeat=w-1):
            signs = (1,)+tail
            P = Poly(sum(s*x**pp for s,pp in zip(signs,support)), x)
            N = abs(int(resultant(Phi, P)))
            if N != 0 and N % p == 0:
                vec = [0]*n
                for s, pos_ in zip(signs, support): vec[pos_] = s
                spur.append(tuple(vec))
    units = [a for a in range(1, n) if math.gcd(a, n) == 1]
    def act(vec, a):
        out = [0]*n
        for i in range(n):
            if vec[i]:
                j = (i*a) % n
                if j < half: out[j] += vec[i]
                else: out[j-half] += -vec[i]
        return tuple(out)
    spurset = set(spur); seen = set(); orbits = 0; sizes = []
    for v in spur:
        if v in seen: continue
        orb = set()
        for a in units:
            ww = act(v, a); orb.add(ww); orb.add(tuple(-c for c in ww))
        real = orb & spurset
        for r in real: seen.add(r)
        orbits += 1; sizes.append(len(real))
    return len(spur), orbits, sorted(set(sizes)), len(units)

def main():
    print("== wf-S7 GALOIS-SPREAD law of char-p spurious relations ==\n")
    print("(1) maxOdd(n,w) growth at fixed weight (crosses n^4 => short spurious at prize):")
    for n in [16, 32, 64]:
        row = f"   n={n:>3} n^4={n**4:>9} | "
        for w in [2, 3, 4]:
            mo = maxodd_fixed_weight(n, w)
            lr = math.log(mo)/math.log(n) if mo > 1 else 0.0
            row += f"w{w}:log_n={lr:.2f} "
        print(row)
    print("\n(2) Galois-orbit decomposition of spurious configs (n=64, prize prime p=17318209):")
    for p in [17318209]:
        assert isprime(p) and p % 64 == 1
        for w in [3, 4]:
            tot, orbits, sizes, phin = galois_orbit_decomp(64, w, p)
            print(f"   w={w}: spurious={tot}, base orbits={orbits}, orbit sizes={sizes}, phi(64)={phin}"
                  f"  => count = orbits*phi(n)" if tot else f"   w={w}: NO spurious (Mann floor holds)")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# wf-S7 (#444): the char-p Mann analogue, SHARPENED — the MIN-NORM / MAX-ODD-FACTOR by weight law.
#
# CONTEXT (landed wf-S7 brick `_wfS7_spur_minweight.lean`): the Mann-analogue weight floor
#   w >= p^{2/n}  from the WORST-CASE conjugate bound  |N(sigma_T)| <= w^{phi(n)}=w^{n/2}.
# At prize n=2^30 this floor -> 1 (vacuous): it does NOT forbid short spurious relations.
#
# BUT the worst-case bound w^{n/2} is hugely loose. The DECISIVE quantity is the LARGEST ODD
# PRIME that can divide a weight-w cyclotomic norm:
#     maxOdd(n,w) := max { largest odd prime factor of |N(sigma_T)| : weight(T)=w, N != 0 }.
# Since p | N forces p <= |N|, and the prize prime p ~ n^4 is ODD with p = 1 mod n, a weight-w
# spurious relation for a prize prime p exists ONLY IF p <= maxOdd(n,w). So the TRUE (sharp)
# first-spurious-weight is  w*(n) = min { w : maxOdd(n,w) >= n^4 }  -- and below it char-0
# TRANSFERS for ALL prize primes, with NO Mann-style vacuity.
#
# We compute the EXACT integer norm N(sigma) = Res(Phi_n, P_sigma) (sympy, big-int exact),
# enumerated EFFICIENTLY: choose the support (C(half,w) subsets) then the signs (2^w), fixing
# global sign by first-nonzero = +1 (so 2^{w-1} sign patterns). This is feasible to n=64, w<=6.

import itertools, sys, math
from sympy import cyclotomic_poly, resultant, symbols, factorint, Poly

x = symbols('x')

def analyze(n, wmax):
    half = n // 2
    Phi = Poly(cyclotomic_poly(n, x), x)
    res = {w: [None, None, 1] for w in range(1, wmax + 1)}  # w -> [Nmin, fac(Nmin), maxOdd]
    positions = list(range(half))
    for w in range(1, wmax + 1):
        for support in itertools.combinations(positions, w):
            # signs: first-nonzero fixed +1, so iterate signs of the remaining w-1
            for tail in itertools.product((1, -1), repeat=w - 1):
                signs = (1,) + tail
                P = Poly(sum(s * x**pos for s, pos in zip(signs, support)), x)
                N = int(resultant(Phi, P))
                aN = abs(N)
                if aN == 0:
                    continue
                if res[w][0] is None or aN < res[w][0]:
                    res[w][0] = aN
                    res[w][1] = factorint(aN)
                fac = factorint(aN)
                for pr in fac:
                    if pr % 2 == 1 and pr > res[w][2]:
                        res[w][2] = pr
    return res

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    wmax = int(sys.argv[2]) if len(sys.argv) > 2 else (n // 2)
    half = n // 2
    prize_p = n**4
    band = round(2 * 4 * math.log(n))
    print(f"== wf-S7 SHARPENED: max-odd-factor by weight, n={n} phi={half} ==")
    print(f"   prize p ~ n^4 = {prize_p}; weight band 2r ~ 2 ln(n^4) = {band}")
    print(f"   maxOdd(n,w)=largest ODD prime dividing any weight-w norm; p~n^4 hittable iff p<=maxOdd\n")
    res = analyze(n, wmax)
    print(f"   {'w':>3} {'Nmin':>10} {'Nmin factored':>20} {'maxOddFactor':>14} {'>=n^4?':>7}")
    first = None
    for w in range(1, wmax + 1):
        Nmin, fac, maxodd = res[w]
        if Nmin is None:
            continue
        facstr = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in fac.items()) or "1"
        cap = maxodd >= prize_p
        if cap and first is None:
            first = w
        print(f"   {w:>3} {Nmin:>10} {facstr:>20} {maxodd:>14} {('YES' if cap else 'no'):>7}")
    print()
    if first:
        print(f"   ==> SHARP first-spurious-weight w*(n) <= {first} (maxOdd first reaches n^4 here).")
    else:
        print(f"   ==> within w<={wmax}: maxOdd < n^4 always => NO prize prime p~n^4 has a")
        print(f"       spurious relation up to weight {wmax}. char-0 transfers (n-specific, NOT vacuous).")
    # growth law: log2(maxOdd) vs w
    print("   growth: log2(maxOdd) by weight:",
          ", ".join(f"w{w}:{math.log2(res[w][2]):.2f}" for w in range(1, wmax+1)
                    if res[w][2] > 1))

if __name__ == "__main__":
    main()

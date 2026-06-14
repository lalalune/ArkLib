#!/usr/bin/env python3
"""
PHASE-ALIGNMENT TOWER PROBE  (#389 deep-moment / sub-Johnson supply wall)

Context: the floor needs sqrt-cancellation among the (p-1)/n Gauss-sum phases
chi-bar(b)*tau(chi), chi in mu_n^perp, at the WORST frequency b*. The fleet
observed (rounds reported on #389, tower-descent technique 1, machine-verified
n=8,16): at b*, the two coset sums S_{a-1}(b*) and S_{a-1}(b*.w) are MAXIMALLY
phase-aligned (cos ~= 1.0000) -- the worst line self-reinforces down the 2-adic
tower, which is exactly why average/moment methods are blind to it.

This probe EXTENDS that observation to n = 32, 64 (a = 5, 6) and asks the sharp
question a non-average proof would need: is the worst-frequency phase alignment
EXACT and STABLE down the whole tower, or does it decay? If alignment is exact
and tower-recursive, that recursion is the non-average structural handle a
Stepanov/descent argument would exploit. PROBE-FIRST: we only measure; any law
gets formalized separately and only if it survives.

S_b = sum_{x in mu_n} e_p(b*x)   (the incomplete character sum at frequency b).
Worst frequency b* = argmax_b |S_b| over b in F_p^*.
Tower step: mu_n -> mu_{n/2} (squares). We compare the phase of S_b over mu_n
against the phase of the two half-coset sums (the two cosets of mu_{n/2} in mu_n).
"""
import cmath, math

def subgroup_2pow(p, a):
    n = 2 ** a
    if (p - 1) % n:
        return None
    g = None
    for c in range(2, p):
        o = 1; y = c % p
        while y != 1:
            y = (y * c) % p; o += 1
            if o > p:
                break
        if o == p - 1:
            g = c; break
    if g is None:
        return None
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    if len(set(H)) != n:
        return None
    return h, H

def ep(p):
    # additive character e_p(t) = exp(2 pi i t / p)
    w = 2 * math.pi / p
    return lambda t: cmath.exp(1j * w * (t % p))

def csum(H, b, e, p):
    return sum(e((b * x) % p) for x in H)

print(f"{'p':>9} {'a':>2} {'n':>4} {'|S_b*|':>9} {'sqrt(n)':>8} "
      f"{'ratio':>6} {'cos(coset0,coset1)@b*':>22} {'cos down-tower':>16}")
print("-" * 96)

for a in range(3, 7):                       # n = 8, 16, 32, 64
    n = 2 ** a
    target = max(4 * n * n, 200)
    p = target
    found = None
    while p < target + 4_000_00:
        p += 1
        if (p - 1) % n:
            continue
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            sg = subgroup_2pow(p, a)
            if sg:
                found = (p, sg)
                break
    if not found:
        print(f"{'--':>9} {a:>2} {n:>4}  no admissible prime found in window")
        continue
    p, (h, H) = found
    e = ep(p)

    # worst frequency b* = argmax_b |S_b|
    best_b, best_mag = 1, -1.0
    for b in range(1, p):
        m = abs(csum(H, b, e, p))
        if m > best_mag:
            best_mag, best_b = m, b
    bstar = best_b

    # split mu_n into the two cosets of mu_{n/2} = squares:
    sq = sorted({(x * x) % p for x in H})           # mu_{n/2}
    sqset = set(sq)
    # a generator coset rep: any element of H not in sq
    rep = next(x for x in H if x not in sqset)
    coset0 = sq
    coset1 = sorted({(rep * x) % p for x in sq})
    S0 = sum(e((bstar * x) % p) for x in coset0)
    S1 = sum(e((bstar * x) % p) for x in coset1)
    # phase alignment of the two half-coset sums at b*
    if abs(S0) > 1e-12 and abs(S1) > 1e-12:
        cos01 = (S0 * S1.conjugate()).real / (abs(S0) * abs(S1))
    else:
        cos01 = float('nan')

    # down-tower: worst freq for mu_{n/2} is bstar*? compare phase of its
    # two sub-coset sums (one more level of descent)
    sq2 = sorted({(x * x) % p for x in sq})         # mu_{n/4}
    if len(sq2) == n // 4 and n >= 8:
        sq2set = set(sq2)
        rep2 = next((x for x in sq if x not in sq2set), None)
        if rep2 is not None:
            T0 = sum(e((bstar * x) % p) for x in sq2)
            T1 = sum(e((bstar * x) % p) for x in sorted({(rep2 * x) % p for x in sq2}))
            if abs(T0) > 1e-12 and abs(T1) > 1e-12:
                cosd = (T0 * T1.conjugate()).real / (abs(T0) * abs(T1))
            else:
                cosd = float('nan')
        else:
            cosd = float('nan')
    else:
        cosd = float('nan')

    ratio = best_mag / math.sqrt(n)
    print(f"{p:>9} {a:>2} {n:>4} {best_mag:>9.3f} {math.sqrt(n):>8.3f} "
          f"{ratio:>6.3f} {cos01:>22.4f} {cosd:>16.4f}")

print()
print("READING: ratio = |S_b*|/sqrt(n). If the worst sum stays ~sqrt(n) (ratio O(1)),")
print("the square-root law HOLDS at the worst frequency = the floor is reachable in")
print("principle. cos(coset0,coset1)@b* near +1 = the fleet's phase-alignment fact;")
print("if it persists at n=32,64 AND down-tower, the alignment is a tower-recursive")
print("structural law (the non-average handle). If ratio grows with n, the worst")
print("frequency BEATS sqrt-cancellation -> evidence the prize conjecture is FALSE.")
print("PROBE ONLY -- no claim until a measured law survives adversarial recheck.")

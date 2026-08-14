#!/usr/bin/env python3
"""
PHASE-ALIGNMENT, PRIZE REGIME (p ~ n^4, the deep-prize n = q^{1/4} scaling).
Successor to probe_phase_alignment_tower.py which ran at p~n^2 (wrong regime).

Question: at the WORST frequency b*, does |S_b*|/sqrt(n) stay O(1) (sqrt law holds
=> floor reachable) or grow (=> conjecture likely FALSE)? And is the down-tower
phase alignment (cos=1.0000 observed at n^2) still exact in the n^4 regime?

n^4 makes a full b-sweep over F_p too expensive for a=5,6 (p ~ 10^6..10^7), so we
restrict the worst-frequency search to the mu_n^perp-relevant frequencies: the worst
b is constant on cosets of mu_n (|S_{b*u}| = |S_b| for u in mu_n), so we sweep ONE
representative per mu_n-coset = (p-1)/n reps, then refine. Still O(p) but with the
heavy inner sum only on the n-element subgroup.
"""
import cmath, math

def find_prime_subgroup(a, regime_exp):
    n = 2 ** a
    # want p ~ n^regime_exp, p prime, n | p-1
    target = int(n ** regime_exp)
    p = max(target, n + 1)
    while True:
        p += 1
        if (p - 1) % n:
            continue
        small_ok = all(p % d for d in range(2, min(int(p ** 0.5) + 1, 100000)))
        if not small_ok:
            continue
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            break
    # generator
    g = None
    for c in range(2, p):
        o = 1; y = c % p
        while y != 1:
            y = (y * c) % p; o += 1
            if o > p: break
        if o == p - 1:
            g = c; break
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    return p, H

def worst_freq(p, H, n):
    w = 2 * math.pi / p
    # |S_b| constant on mu_n-cosets; sweep coset reps b = 1..(p-1) but step by
    # skipping mu_n multiples is hard, so just sweep all b and keep max (a<=6 ok
    # for p up to ~2e7 if we vectorize lightly via precomputed phase table).
    best_b, best = 1, -1.0
    # precompute e_p(t) lazily is too slow; do direct but only n terms each.
    Hl = H
    for b in range(1, p):
        s_re = 0.0; s_im = 0.0
        for x in Hl:
            ang = w * ((b * x) % p)
            s_re += math.cos(ang); s_im += math.sin(ang)
        m = s_re * s_re + s_im * s_im
        if m > best:
            best = m; best_b = b
    return best_b, math.sqrt(best)

def cos_split(p, sub, bstar, rep):
    w = 2 * math.pi / p
    def S(group):
        r = i = 0.0
        for x in group:
            a = w * ((bstar * x) % p); r += math.cos(a); i += math.sin(a)
        return complex(r, i)
    sqset = set(sub)
    c0 = sub
    c1 = [(rep * x) % p for x in sub]
    S0, S1 = S(c0), S(c1)
    if abs(S0) > 1e-9 and abs(S1) > 1e-9:
        return (S0 * S1.conjugate()).real / (abs(S0) * abs(S1))
    return float('nan')

print("PRIZE-REGIME (p ~ n^4) phase-alignment probe")
print(f"{'p':>11} {'a':>2} {'n':>4} {'|S_b*|':>9} {'sqrt(n)':>8} {'ratio':>6} {'cos@b*':>8} {'cos tower':>10}")
print("-" * 72)
# a=3,4 feasible at n^4 (p ~ 4096, 65536); a=5 (p~1e6) heavier; a=6 (p~1.6e7) skip full sweep
for a in [3, 4, 5]:
    n = 2 ** a
    p, H = find_prime_subgroup(a, 4.0)
    bstar, mag = worst_freq(p, H, n)
    sq = sorted({(x * x) % p for x in H})
    sqset = set(sq)
    rep = next(x for x in H if x not in sqset)
    cos01 = cos_split(p, sq, bstar, rep)
    sq2 = sorted({(x * x) % p for x in sq})
    rep2 = next((x for x in sq if x not in set(sq2)), None)
    cosd = cos_split(p, sq2, bstar, rep2) if rep2 is not None else float('nan')
    print(f"{p:>11} {a:>2} {n:>4} {mag:>9.3f} {math.sqrt(n):>8.3f} {mag/math.sqrt(n):>6.3f} {cos01:>8.4f} {cosd:>10.4f}")

print()
print("If ratio stays O(1) in n^4 regime and cos stays 1.0000 -> sqrt law + tower")
print("self-similarity hold where the prize lives = real handle. If ratio grows -> FALSE signal.")

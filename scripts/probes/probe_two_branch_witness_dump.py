#!/usr/bin/env python3
"""Witness dump for the two-branch countermodel Lean brick (#389).

Fixed shape chosen for kernel-friendliness:
  p = 101, D = {0..n-1} (interval domain, n = 80), A = {0..39}, B = {40..79},
  w(x) = x^2 + (c if x in B else 0).
Sweeps c to maximize the 4-rich line count; emits the Lean `lineDataN` literal
(line slope, intercept, and the 4 domain INDICES, which here equal the domain
points themselves).  Verifies via full census: every line meets the graph in
<= 4 points and the 4-rich lines are exactly the emitted ones.

Output (2026-06-13): best c = 29, 107 four-rich lines, Sum a = 428 > 160 = 2n;
this is the data embedded in TwoBranchSupplyCountermodel.lean.
"""

from itertools import combinations
from collections import defaultdict

P = 101
N = 80
A = list(range(40))
B = list(range(40, 80))


def legendre(a, p):
    if a % p == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r


def lines_for(c):
    Bs = set(B)
    out = []
    inv2 = pow(2, -1, P)
    for x1, x2 in combinations(A, 2):
        disc = ((x1 - x2) ** 2 - 4 * c) % P
        if disc == 0 or legendre(disc, P) != 1:
            continue
        r = sqrt_mod(disc, P)
        s = (x1 + x2) % P
        x3, x4 = (s + r) * inv2 % P, (s - r) * inv2 % P
        if x3 == x4 or x3 not in Bs or x4 not in Bs:
            continue
        out.append(((x1 + x2) % P, (-x1 * x2) % P,
                    tuple(sorted([x1, x2, x3, x4]))))
    return out


def census(c):
    w = {x: (x * x + (c if x >= 40 else 0)) % P for x in range(N)}
    pair_count = defaultdict(int)
    for x, y in combinations(range(N), 2):
        s = ((w[x] - w[y]) * pow(x - y, -1, P)) % P
        b = (w[x] - s * x) % P
        pair_count[(s, b)] += 1
    amax, rich = 0, {}
    for key, pc in pair_count.items():
        a = int((1 + (1 + 8 * pc) ** 0.5) / 2 + 1e-9)
        amax = max(amax, a)
        if a >= 4:
            rich[key] = a
    return rich, amax


best = None
for c in range(1, 30):
    ls = lines_for(c)
    if best is None or len(ls) > len(best[1]):
        best = (c, ls)
c, ls = best
rich, amax = census(c)
print(f"best c = {c}: {len(ls)} four-rich lines; census: {len(rich)} rich, max_a = {amax}")
assert amax <= 4, "cap broken"
assert len(rich) == len(ls), (len(rich), len(ls))
assert set((s, b) for s, b, _ in ls) == set(rich), "construction != census"
sum_a = 4 * len(ls)
print(f"Sum a = {sum_a} vs 2n = {2 * N}  ->  {'VIOLATED' if sum_a > 2 * N else 'ok'}")

print("\n-- Lean data (slope, intercept, indices):")
entries = []
for s, b, T in ls:
    t = ", ".join(str(x) for x in T)
    entries.append(f"  (({s}, {b}), {{{t}}})")
print("def lineDataN : List ((ℕ × ℕ) × Finset (Fin 80)) := [\n"
      + ",\n".join(entries) + "\n]")

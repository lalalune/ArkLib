#!/usr/bin/env python3
"""
PROBE: find the cleanest RECURSION for #classInjectiveTransversals over a
no-2-torsion negation-closed G of order n, to drive a Lean induction on r.

ClassInjective t (t : Fin r -> G): forall i!=j, t i != t j AND t i != -t j.
Equivalently the r values lie in r DISTINCT antipodal classes {g,-g}.

Candidate recursions (extend a length-(r-1) class-injective tuple by one more value):
  R1 (append):  #CI(r) = #CI(r-1) * (n - 2*(r-1))
     [the r-th value avoids the 2*(r-1) values {t k, -t k : k<r-1}]
  closed form:  #CI(r) = prod_{i<r} (n - 2*i) = 2^r * (n/2)_r.
Verify both, and that the per-step multiplier is exactly n - 2*(r-1) regardless
of WHICH class-injective prefix (uniform extension count -> clean Lean induction).
"""
from itertools import product


def neg(x, n):
    return (x + n // 2) % n


def class_injective(t, n):
    r = len(t)
    for i in range(r):
        for j in range(r):
            if i != j and (t[i] == t[j] or t[i] == neg(t[j], n)):
                return False
    return True


def count_ci(n, r):
    if r == 0:
        return 1
    return sum(1 for t in product(range(n), repeat=r) if class_injective(t, n))


def falling(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


print("=== R1 recursion #CI(r) = #CI(r-1)*(n-2(r-1)) and closed form 2^r*(n/2)_r ===")
ok = True
for n in [4, 8, 16]:
    for r in range(0, 4):
        c = count_ci(n, r)
        closed = (2 ** r) * falling(n // 2, r)
        rec = count_ci(n, r - 1) * (n - 2 * (r - 1)) if r >= 1 else 1
        match = (c == closed == rec)
        ok &= match
        print(f"n={n:>3} r={r}: #CI={c:>6} closed={closed:>6} rec={rec:>6} match={match}")

print("=== uniform extension: every class-injective prefix extends in exactly n-2(r-1) ways ===")
uni = True
for n in [4, 8]:
    for r in range(1, 4):
        prefixes = [t for t in product(range(n), repeat=r - 1) if class_injective(t, n)]
        exts = set()
        for t in prefixes:
            cnt = sum(1 for v in range(n) if class_injective(t + (v,), n))
            exts.add(cnt)
        expect = n - 2 * (r - 1)
        good = (exts == {expect}) or (len(prefixes) == 0)
        uni &= good
        print(f"n={n} r={r}: extension counts={exts} expect={expect} uniform={good}")
print("ALL:", ok and uni)

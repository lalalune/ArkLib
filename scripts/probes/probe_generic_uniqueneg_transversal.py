#!/usr/bin/env python3
"""
PROBE (prize-grind): the UniqueNeg <-> transversal-class-injectivity reduction.

CLAIM: for a fixed pairing sigma0, buildConsistent sigma0 t  (lower slots = t,
upper slots = -t-of-partner) lies in genericAntipodalSet  iff  the transversal
map t : Fin r -> G is "class-injective":
    forall i != j,  t i != t j   AND   t i != -t j.
(i.e. the r transversal values lie in r DISTINCT antipodal classes {g,-g}.)

If true, then  #genericAntipodalSet(G, sigma0) == #{ class-injective t }, which
for a no-2-torsion negation-closed G of order n is (n/2)_r * 2^r (choose r of the
n/2 classes, ordered, times 2 signs each).

We verify BOTH:
  (A) the iff between UniqueNeg(buildConsistent t) and class-injective(t);
  (B) #{class-injective t} == (n/2)_r * 2^r.
Model mu_n = Z_n additive, neg(x) = x + n/2.  NEVER n=q-1.
"""
from itertools import product


def falling(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


def neg(x, n):
    return (x + n // 2) % n


def reference_pairing(r):
    sig = list(range(2 * r))
    for k in range(r):
        sig[2 * k], sig[2 * k + 1] = 2 * k + 1, 2 * k
    return sig


def lower_half(sig):
    # positions i with i < sig[i]
    return [i for i in range(len(sig)) if i < sig[i]]


def build_consistent(sig, t, n):
    # lower slots get t in order; upper slot i gets -t[partner-index]
    L = lower_half(sig)
    idx_of = {i: k for k, i in enumerate(L)}  # transversal index
    c = [None] * len(sig)
    for k, i in enumerate(L):
        c[i] = t[k]
    for i in range(len(sig)):
        if c[i] is None:
            # i is upper; partner sig[i] is in L
            c[i] = neg(t[idx_of[sig[i]]], n)
    return tuple(c)


def unique_neg(c, n):
    m = len(c)
    for i in range(m):
        target = neg(c[i], n)
        wit = [j for j in range(m) if c[j] == target]
        if len(wit) != 1:
            return False
    return True


def class_injective(t, n):
    r = len(t)
    for i in range(r):
        for j in range(r):
            if i != j:
                if t[i] == t[j] or t[i] == neg(t[j], n):
                    return False
    return True


print("=== (A) iff: UniqueNeg(build t) <-> class_injective(t) ===")
iff_ok = True
for n, r in [(4, 1), (4, 2), (8, 1), (8, 2), (8, 3), (16, 2)]:
    sig = reference_pairing(r)
    for t in product(range(n), repeat=r):
        c = build_consistent(sig, t, n)
        lhs = unique_neg(c, n)
        rhs = class_injective(t, n)
        if lhs != rhs:
            iff_ok = False
            print("MISMATCH", n, r, t, "UN=", lhs, "CI=", rhs)
print("IFF holds:", iff_ok)

print("=== (B) #class-injective t == (n/2)_r * 2^r ===")
ct_ok = True
print(f"{'n':>4} {'r':>3} {'#CI':>8} {'(n/2)_r*2^r':>14} {'match':>6}")
for n, r in [(4, 1), (4, 2), (4, 3), (8, 1), (8, 2), (8, 3), (16, 1), (16, 2)]:
    cnt = sum(1 for t in product(range(n), repeat=r) if class_injective(t, n))
    pred = falling(n // 2, r) * (2 ** r)
    match = (cnt == pred)
    ct_ok &= match
    print(f"{n:>4} {r:>3} {cnt:>8} {pred:>14} {str(match):>6}")
print("COUNT holds:", ct_ok)
print("ALL:", iff_ok and ct_ok)

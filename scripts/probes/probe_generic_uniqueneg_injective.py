#!/usr/bin/env python3
"""
PROBE (prize-grind): confirm the Lean proof spine
   UniqueNeg(buildConsistent t)  <->  Injective(buildConsistent t)  <->  ClassInjective t
on a NO-2-TORSION negation-closed G (mu_n, n=2^k, so -g != g for all g).

This justifies proving the equivalence via injectivity (clean Finset.card route)
rather than slot enumeration.
"""
from itertools import product


def neg(x, n):
    return (x + n // 2) % n


def reference_pairing(r):
    sig = list(range(2 * r))
    for k in range(r):
        sig[2 * k], sig[2 * k + 1] = 2 * k + 1, 2 * k
    return sig


def lower_half(sig):
    return [i for i in range(len(sig)) if i < sig[i]]


def build_consistent(sig, t, n):
    L = lower_half(sig)
    idx_of = {i: k for k, i in enumerate(L)}
    c = [None] * len(sig)
    for k, i in enumerate(L):
        c[i] = t[k]
    for i in range(len(sig)):
        if c[i] is None:
            c[i] = neg(t[idx_of[sig[i]]], n)
    return tuple(c)


def unique_neg(c, n):
    for i in range(len(c)):
        tgt = neg(c[i], n)
        if sum(1 for j in range(len(c)) if c[j] == tgt) != 1:
            return False
    return True


def injective(c):
    return len(set(c)) == len(c)


def class_injective(t, n):
    r = len(t)
    for i in range(r):
        for j in range(r):
            if i != j and (t[i] == t[j] or t[i] == neg(t[j], n)):
                return False
    return True


ok = True
for n, r in [(4, 1), (4, 2), (8, 1), (8, 2), (8, 3), (16, 2)]:
    sig = reference_pairing(r)
    for t in product(range(n), repeat=r):
        c = build_consistent(sig, t, n)
        un = unique_neg(c, n)
        inj = injective(c)
        ci = class_injective(t, n)
        if not (un == inj == ci):
            ok = False
            print("MISMATCH", n, r, t, "UN", un, "INJ", inj, "CI", ci)
print("UniqueNeg == Injective == ClassInjective :", ok)

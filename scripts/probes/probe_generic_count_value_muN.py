#!/usr/bin/env python3
"""
PROBE (prize-grind, value of the per-sigma generic count for mu_n=2^k):
verify  #genericAntipodalSet(mu_n, sigma0) == (n/2)_r * 2^r  for a reference
fixed-point-free involution sigma0 (the adjacent pairing (0 1)(2 3)...).

genericAntipodalSet(G, sigma) = { c : Fin(2r) -> G |
   (forall i, c(sigma i) = -c i)  AND  UniqueNeg c }
UniqueNeg c = forall i, exists! j, c j = -c i.

We model mu_n (n=2^k) as Z_n additively with negation = +n/2 (the order-2
element), exactly the no-fixed-point negation of a 2-power cyclic group.
NEVER n=q-1 (this is intrinsic group combinatorics, n is the subgroup order).
"""
from itertools import product


def falling(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


def neg(x, n):       # negation in mu_n = mult by order-2 elt = +n/2 in Z_n
    return (x + n // 2) % n


def unique_neg(c, n):
    # forall i exists! j : c[j] == neg(c[i])
    m = len(c)
    for i in range(m):
        t = neg(c[i], n)
        wit = [j for j in range(m) if c[j] == t]
        if len(wit) != 1:
            return False
    return True


def reference_pairing(r):
    # sigma0 = (0 1)(2 3)...(2r-2  2r-1): swap 2k <-> 2k+1
    sig = list(range(2 * r))
    for k in range(r):
        sig[2 * k], sig[2 * k + 1] = 2 * k + 1, 2 * k
    return sig


def count_generic(n, r):
    sig = reference_pairing(r)
    cnt = 0
    for c in product(range(n), repeat=2 * r):
        ok = all(c[sig[i]] == neg(c[i], n) for i in range(2 * r))
        if not ok:
            continue
        if unique_neg(c, n):
            cnt += 1
    return cnt


print(f"{'n':>4} {'r':>3} {'count':>10} {'(n/2)_r*2^r':>14} {'match':>6}")
ok_all = True
cases = [(4, 1), (4, 2), (4, 3), (8, 1), (8, 2), (8, 3), (16, 1), (16, 2)]
for n, r in cases:
    cnt = count_generic(n, r)
    pred = falling(n // 2, r) * (2 ** r)
    match = (cnt == pred)
    ok_all &= match
    print(f"{n:>4} {r:>3} {cnt:>10} {pred:>14} {str(match):>6}")
print("ALL MATCH:", ok_all)

#!/usr/bin/env python3
"""#389 monomial supply witness (the generic-density phase), exact.

w = x^t at t = k+m+1 over a domain D in F_q. (k,m) = (2,1): t = 4, cap 4 <= 6.
A 4-subset T of D is an explainable core of w iff x^4 mod prod_{i in T}(X - x_i)
has degree < 2, iff e1(T) = e2(T) = 0 (the vanishing remainder window).

P1 (direct, small q): count via triple-enumeration + agreement-profile audit of
    the cap (all q^2 lines) at q in {31, 127, 257}, D = full units.
P2 (pair-hash, production shape): count on mu_4096 in F_12289 (g = 11^3 order 4096)
    via the partition identity: {x1..x4} with e1=e2=0 <=> any pair-partition
    (P1,P2) has s' = -s, p' = s^2 - p; each 4-set has 3 partitions x 2 orders.

Pre-registered expectations: counts ~ C(n,4)/q^2; mu_4096 count >> 2n (refuting
linear supply at n = Theta(q)); cap profile max = 4.
"""
from collections import Counter
from itertools import combinations


def count_rich_direct(q, D):
    cnt = 0
    Dset = set(D)
    for (x1, x2, x3) in combinations(sorted(D), 3):
        x4 = (-(x1 + x2 + x3)) % q
        if x4 in Dset and x4 > x3:
            e2 = (x1*x2 + x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4) % q
            if e2 == 0:
                cnt += 1
    return cnt


def agreement_profile(q, D):
    prof = Counter()
    for a in range(q):
        for b in range(q):
            c = sum(1 for x in D if (x**4 - a - b*x) % q == 0)
            if c:
                prof[c] += 1
    return dict(sorted(prof.items()))


def count_rich_pairhash(q, D):
    Dset = set(D)
    Dl = sorted(D)
    pairs = Counter()
    for i, xi in enumerate(Dl):
        for xj in Dl[i+1:]:
            pairs[((xi + xj) % q, xi * xj % q)] += 1
    total = 0
    for (s, p), c in pairs.items():
        total += c * pairs.get(((-s) % q, (s*s - p) % q), 0)
    bad = 0
    for a in Dl:
        for b in Dl:
            if a == b:
                continue
            s = (a + b) % q
            c = (-s - a) % q
            if c in Dset and c != a and c != b and (a*c) % q == (s*s - a*b) % q:
                bad += 1
    assert (total - bad) % 6 == 0
    return (total - bad) // 6


def main():
    print("== P1: direct counts + cap audit ==")
    for q in (31, 127, 257):
        D = list(range(1, q))
        n = len(D)
        c = count_rich_direct(q, D)
        pred = (n*(n-1)*(n-2)*(n-3)//24) / q**2
        print(f"q={q} n={n}: cores={c}  pred={pred:.1f}  ratio={c/n:.2f}n")
    prof = agreement_profile(127, list(range(1, 127)))
    print(f"q=127 agreement profile: {prof}")
    assert max(prof) == 4, "cap violated!"
    assert prof[4] == count_rich_direct(127, list(range(1, 127)))

    print("== P2: the production shape mu_4096 in F_12289 ==")
    q = 12289
    g = pow(11, (q - 1) // 4096, q)
    D, x = [], 1
    for _ in range(4096):
        D.append(x)
        x = x * g % q
    assert len(set(D)) == 4096
    cnt = count_rich_pairhash(q, D)
    n = 4096
    pred = (n*(n-1)*(n-2)*(n-3)//24) / q**2
    print(f"q={q} n={n}: cores={cnt}  pred={pred:.0f}  ratio={cnt/n:.2f}n  (2n={2*n})")
    # cross-validate pair-hash against direct on a small instance
    q2 = 127
    direct = count_rich_direct(q2, list(range(1, q2)))
    hashed = count_rich_pairhash(q2, list(range(1, q2)))
    assert direct == hashed, (direct, hashed)
    print(f"cross-validation q=127: direct={direct} == pairhash={hashed}  OK")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""probe_fit_family_bound.py — the all-witness ownership floor (#371, fit-family bound).

Pre-registered claims (the superadditivity theorem behind the exact subset law):

  C1  (fit-family bound)  for every word u on a w-point node set S (distinct nodes)
      that is NOT degree-d-fit on S:
        #{T subset S : |T| = d+2, u fit on T} <= C(w-1, d+2),
      equivalently #non-fit >= C(w-1, d+1).  Exhaustive over u at:
        d=0: p=5,  w=4,5 ; d=1: p=5, w=5,6 ; d=2: p=3, w=6,7.
      Expected violations: 0.

  C2  (attainment)  the bound is attained exactly by the single-deviation words
      (u = poly except at one point).  Report: max #fit, #attaining words,
      whether all attaining words are single-deviation.

  C3  (block structure)  fit (d+2)-subsets decompose as the disjoint union of all
      (d+2)-subsets of the maximal fit sets; maximal fit sets pairwise intersect
      in <= d points.  Expected violations: 0.

Exit 0 iff all pre-registered checks pass.
"""
import itertools
import sys
from math import comb

FAIL = 0


def inv_mod(a, p):
    return pow(a, p - 2, p)


def interpolate_fits(xs, ys, d, p, T):
    """Is (xs[i], ys[i]) for i in T matched by a poly of degree <= d?"""
    T = sorted(T)
    if len(T) <= d + 1:
        return True
    base = T[: d + 1]
    # Lagrange through base, check rest
    def ev(x):
        total = 0
        for i in base:
            num, den = 1, 1
            for j in base:
                if j == i:
                    continue
                num = num * ((x - xs[j]) % p) % p
                den = den * ((xs[i] - xs[j]) % p) % p
            total = (total + ys[i] * num * inv_mod(den, p)) % p
        return total
    return all(ev(xs[i]) == ys[i] % p for i in T[d + 1:])


def run_case(p, w, d):
    global FAIL
    assert w <= p, "need w <= p for distinct nodes"
    xs = list(range(w))  # distinct nodes in F_p
    k = d + 2
    bound = comb(w - 1, k)
    S = list(range(w))
    maxfit, attain, attain_sd, viol1, viol3 = 0, 0, 0, 0, 0
    for ys in itertools.product(range(p), repeat=w):
        if interpolate_fits(xs, ys, d, p, S):
            continue  # u fit on S: out of scope
        fits = [T for T in itertools.combinations(S, k)
                if interpolate_fits(xs, ys, d, p, T)]
        nf = len(fits)
        if nf > bound:
            viol1 += 1
        if nf > maxfit:
            maxfit, attain, attain_sd = nf, 0, 0
        if nf == maxfit:
            attain += 1
            # single-deviation test: exists j with u fit on S \ {j}
            if any(interpolate_fits(xs, ys, d, p, [i for i in S if i != j])
                   for j in S):
                attain_sd += 1
        # C3 block structure
        maximal = []
        for size in range(w - 1, k - 1, -1):
            for A in itertools.combinations(S, size):
                if interpolate_fits(xs, ys, d, p, A):
                    if not any(set(A) <= set(B) for B in maximal):
                        maximal.append(A)
        cover = set()
        ok3 = True
        for A in maximal:
            subs = set(itertools.combinations(sorted(A), k))
            if cover & subs:
                ok3 = False  # not disjoint
            cover |= subs
        if cover != set(fits):
            ok3 = False
        for A, B in itertools.combinations(maximal, 2):
            if len(set(A) & set(B)) > d:
                ok3 = False
        if not ok3:
            viol3 += 1
    status = "OK" if (viol1 == 0 and viol3 == 0) else "FAIL"
    if viol1 or viol3:
        FAIL = 1
    print(f"  [{status}] p={p} w={w} d={d}: bound C({w-1},{k})={bound}, "
          f"max #fit={maxfit}, attained by {attain} words "
          f"(single-dev: {attain_sd}), viol C1={viol1} C3={viol3}")


def main():
    run_case(5, 4, 0)
    run_case(5, 5, 0)
    run_case(5, 5, 1)
    run_case(7, 6, 1)
    run_case(7, 6, 2)
    run_case(7, 7, 2)
    sys.exit(FAIL)


if __name__ == "__main__":
    main()

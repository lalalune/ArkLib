#!/usr/bin/env python3
"""Probe (#444): the translation orbit of an ODD-card subset E of Z/2^a has size EXACTLY 2^a.

This is the cardinality conclusion of CliqueOrbitFreeness.prize_regime_fixed_eq_zero (which
proves only that the STABILIZER is trivial, j=0).  Orbit-stabilizer then gives |orbit| = 2^a.
Even-card subsets can have a NONTRIVIAL stabilizer => smaller orbit (the contrast).

NEVER n = q-1: this is pure char-0 cyclic-group combinatorics on Z/2^a, the prize 2-power tower.
"""
from itertools import combinations


def orbit_size(E, n):
    seen = set()
    for j in range(n):
        seen.add(frozenset((x + j) % n for x in E))
    return len(seen)


def main():
    print("a |  n | ALL odd-card E have orbit = n? | even-card counterexample (size, orbit<n)")
    for a in range(2, 7):
        n = 2 ** a
        odd_ok = True
        for sz in (1, 3, 5, 7):
            if sz > n:
                continue
            cnt = 0
            for E in combinations(range(n), sz):
                if orbit_size(E, n) != n:
                    odd_ok = False
                    print(f"  ODD FAIL a={a} sz={sz} E={E} orbit={orbit_size(E, n)}")
                cnt += 1
                if cnt >= 60:
                    break
        ce = None
        for sz in (2, 4):
            for E in combinations(range(n), sz):
                os = orbit_size(E, n)
                if os < n:
                    ce = (sz, os, E)
                    break
            if ce:
                break
        verdict = "PASS" if odd_ok else "FAIL"
        print(f"{a} | {n:2d} | odd all orbit=n: {odd_ok} ({verdict}) | even ctrex: {ce}")
    print("\nVERDICT: ODD-card => orbit size EXACTLY n on Z/2^a; EVEN-card can have smaller orbit.")


if __name__ == "__main__":
    main()

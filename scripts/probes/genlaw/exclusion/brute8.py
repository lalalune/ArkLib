#!/usr/bin/env python3
"""Third, pure-Python implementation of raw feasibility at s=8 (all odd r).
Independent of both diag.c (axis logic) and brute.c (C combination walk):
uses itertools.combinations and collections.Counter on the literal multiset.
Prints per-class records and totals in brute.c's format for diffing.
"""
import sys
from itertools import combinations

def run(s, r):
    n, b = 2 * s, (s + 1 - r) // 2
    nclasses = waysum = 0
    out = []
    for O in combinations(range(s), r):
        comp = [f for f in range(s) if f not in O]
        for m in range(1 << (r - 1)):
            a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
            base = [0] * n
            for i in range(r):
                for j in range(i + 1, r):
                    base[(a[i] + a[j]) % n] += 1
            for o in O:
                base[(2 * o) % n] += 1
            base[(3 * s // 2) % n] += 1
            w = 0
            for B in combinations(comp, b):
                cnt = base[:]
                for f in B:
                    cnt[(2 * f) % n] += 1
                if all(cnt[t] == cnt[t + s] for t in range(s)):
                    w += 1
            if w:
                nclasses += 1
                waysum += w
                out.append("REC " + " ".join(map(str, O)) + f" | m {m} | w {w}")
    for line in out:
        print(line)
    print(f"BRUTE TOTAL s {s} r {r} b {b} classes {nclasses} waysum {waysum}")

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))

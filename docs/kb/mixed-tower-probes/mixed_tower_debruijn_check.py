#!/usr/bin/env python3
"""
Independent de Bruijn decomposition check (separate algorithm from the DFS
family generation in mixed_tower_probe.py):

 * recomputes the FULL e_1 = 0 fiber at n = 24 (exhaustive, 2^24) and n = 36
   (exhaustive meet-in-the-middle) in F_p,
 * runs a per-member BACKTRACKING decomposer into disjoint rotated prime
   packets (mu_2 pairs {i, i+n/2}, mu_3 triples {i, i+n/3, i+2n/3}),
   memoized on submasks — all members at n=24, all 10^6 members at n=36.
 * also verifies the converse direction independently: every disjoint
   prime-packet union has p_1 = 0 (trivial but checked numerically).
 * demonstrates the CRT disjointness obstruction: at n=36 a mu_4-coset
   (a full CRT column) and a mu_9-coset (a full CRT row) always intersect,
   so the naive "multiset of packet sizes summing to w" count over-predicts
   (no weight-13 = 4+9 member at window t=3).
"""
import sys, time
import numpy as np
from collections import defaultdict

sys.path.insert(0, "/tmp")
from mixed_tower_probe import (find_prime_1mod, primitive_root_of_unity,
                               e1_fiber_exhaustive, e1_fiber_mitm,
                               power_matrix, predicted_family, min_allowed)

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

def prime_blocks_per_elem(n):
    per = defaultdict(list)
    blocks = set()
    for i in range(n // 2):
        m = (1 << i) | (1 << (i + n // 2))
        blocks.add(m)
    for i in range(n // 3):
        m = (1 << i) | (1 << (i + n // 3)) | (1 << (i + 2 * n // 3))
        blocks.add(m)
    for b in blocks:
        lo = (b & -b).bit_length() - 1
        per[lo].append(b)
    return per, blocks

def make_decomposer(n):
    per, _ = prime_blocks_per_elem(n)
    cache = {0: True}
    def dec(mask):
        if mask in cache: return cache[mask]
        lo = (mask & -mask).bit_length() - 1
        ok = False
        for b in per.get(lo, ()):
            if b & mask == b and dec(mask ^ b):
                ok = True
                break
        cache[mask] = ok
        return ok
    return dec

def main():
    p = find_prime_1mod(72, 10**9)
    rng = np.random.default_rng(232)
    for n in (24, 36):
        z = primitive_root_of_unity(n, p)
        mem = e1_fiber_exhaustive(n, p, z) if n <= 24 else e1_fiber_mitm(n, p, z)
        log(f"n={n}: |e1-fiber| = {len(mem)} (exhaustive census)")
        dec = make_decomposer(n)
        bad = [int(m) for m in mem if not dec(int(m))]
        log(f"n={n}: members NOT decomposable into disjoint prime packets: "
            f"{len(bad)}  {'<-- VIOLATION' if bad else '(de Bruijn holds, all members)'}")
        if bad[:3]: log("   examples:", [hex(b) for b in bad[:3]])
        # converse: random prime-packet unions have p_1 = 0
        per, blocks = prime_blocks_per_elem(n)
        bl = sorted(blocks)
        zpow = [pow(z, i, p) for i in range(n)]
        fails = 0
        for _ in range(20000):
            mask = 0
            for j in rng.permutation(len(bl))[: rng.integers(1, len(bl))]:
                if bl[j] & mask == 0: mask |= bl[j]
            s = 0
            mm, i = mask, 0
            while mm:
                if mm & 1: s += zpow[i]
                mm >>= 1; i += 1
            if s % p != 0: fails += 1
        log(f"n={n}: converse sample (20000 random packet unions, p_1=0): "
            f"{'OK' if fails == 0 else f'{fails} FAILURES'}")

    # naive multiset-of-sizes count over-predicts: mu_4 + mu_9 at n=36, t=3
    fam = predicted_family(36, 3)
    w13 = [m for m in fam if int(m).bit_count() == 13]
    w19 = [m for m in fam if int(m).bit_count() == 19]
    log(f"n=36, t=3 (Dmin={list(min_allowed(36,3))}): weight-13 members = {len(w13)}, "
        f"weight-19 members = {len(w19)} (naive size-multiset count predicts >0: "
        f"13=4+9, 19=4+6+9; CRT row/column obstruction kills them)")
    # show mu_4 and mu_9 cosets always intersect
    inter_ok = True
    for r in range(9):
        c4 = set((r + 9*i) % 36 for i in range(4))
        for u in range(4):
            c9 = set((u + 4*i) % 36 for i in range(9))
            if not (c4 & c9): inter_ok = False
    log(f"every mu_4-coset meets every mu_9-coset in mu_36: {inter_ok}")

if __name__ == "__main__":
    main()

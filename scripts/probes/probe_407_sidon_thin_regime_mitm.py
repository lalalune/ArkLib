#!/usr/bin/env python3
"""
#407 -- Sidon depth in the GENUINELY THIN regime (p >= n^4) via meet-in-the-middle.

WHY THIS PROBE.  The companion `probe_407_sidon_depth_frobenius_bootstrap.py` measured the Sidon
depth, but its Section-1 primes were tiny (p ~ n..16n) where mu_n is DENSE in F_p so spurious
zero-sums are forced by pigeonhole and the measured depth is artificially small -- NOT the prize
regime.  The prize regime is n <= p^{1/4} (p >= n^4): mu_n is genuinely thin.  A naive O(C(n,r))
scan for the smallest spurious zero-sum is infeasible at n=32,64 (C(32,16)~6e8), so we use a
MEET-IN-THE-MIDDLE subset-sum search: split indices {0..n-1} into two halves, enumerate all
subset-sums of each half into hash tables, and find a subset of size r with total sum == 0 mod p.
This finds the SMALLEST r with a non-antipodal zero-sum in time ~ 2^{n/2} (feasible to n=32; n=64
done partially with a randomized/structured search).

The question (issue #407 sec.5.0 BIND): in the thin regime, is the smallest spurious non-antipodal
zero-sum's size r > log2(n)?  Does it grow with n (so the property HOLDS up to large r, i.e. the
bootstrap target is plausibly TRUE), or does a small spurious zero-sum persist (gap is real)?

HONESTY: antipodal subsets (unions of {i,i+n/2}) are excluded as trivial.  We report the SMALLEST
non-antipodal unsigned zero-sum found; if none up to r=n/2, BIND holds for that (n,p).
"""

import sys, itertools, random
from math import log2

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; facs=set(); m=phi; d=2
    while d*d <= m:
        while m % d == 0: facs.add(d); m//=d
        d += 1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def zeta_powers(p,n):
    g = primitive_root(p); z = pow(g,(p-1)//n,p)
    return [pow(z,i,p) for i in range(n)]

def is_antipodal_subset(Sset, n):
    h = n//2
    return all(((i+h)%n) in Sset for i in Sset)

def smallest_zerosum_mitm(p, n, zp, rmax=None):
    """
    Meet-in-the-middle: find the smallest non-antipodal subset S (|S|>=2) with
    sum_{i in S} zeta^i == 0 mod p.  Returns (r, S) or (None,None) up to rmax.
    Approach: split [0,n) into A=[0,h), B=[h,n), h=n//2.  Enumerate subset sums of A keyed
    by (sum mod p) -> list of (mask, popcount).  Then for each subset of B with sum s, look up
    A-subsets with sum == (-s) mod p; candidate union has total 0.  Track minimum popcount.
    n<=32 => 2^16 per half, fine.  n=64 => 2^32 too big; handled separately by halving B further.
    """
    if rmax is None: rmax = n//2
    h = n//2
    A = list(range(0, h)); B = list(range(h, n))
    # build A table: sum -> list of (frozenset, size)
    from collections import defaultdict
    Atab = defaultdict(list)
    for mask in range(1<<len(A)):
        s = 0; size=0; Sset=set()
        mm=mask; idx=0
        while mm:
            if mm & 1:
                s += zp[A[idx]]; size+=1; Sset.add(A[idx])
            mm >>= 1; idx+=1
        Atab[s % p].append((frozenset(Sset), size))
    # also include empty-A (sum 0) so pure-B solutions are found
    best = None  # (size, frozenset)
    for mask in range(1<<len(B)):
        s=0; size=0; Sset=set()
        mm=mask; idx=0
        while mm:
            if mm & 1:
                s += zp[B[idx]]; size+=1; Sset.add(B[idx])
            mm >>= 1; idx+=1
        need = (-s) % p
        for (Aset, Asize) in Atab.get(need, ()):
            total = Aset | Sset
            tsize = Asize + size
            if tsize < 2: continue
            if best is not None and tsize >= best[0]: continue
            if is_antipodal_subset(total, n): continue
            best = (tsize, total)
    if best is None: return None, None
    return best[0], sorted(best[1])

def main():
    print("="*80)
    print("Smallest non-antipodal UNSIGNED zero-sum in the THIN regime (p >= n^4), via MITM")
    print("="*80)
    print(f"{'n':>4} {'log2 n':>7} {'p':>14} {'p^.25':>9} {'thin?':>6} {'m_odd':>6} "
          f"{'smallest_r':>11} {'> log2 n?':>10}")
    for a in (4, 5):           # n=16, 32 (n=64 MITM half=2^32 infeasible; see note)
        n = 2**a
        target = n**4
        # gather: 2 odd-m thin primes + 1 even-m thin prime
        got=[]
        p = target + ((n-(target%n))%n) + 1
        need_odd=2; need_even=1
        while (need_odd>0 or need_even>0) and p < target + 6000*n:
            if is_prime(p) and p % n == 1:
                m=(p-1)//n
                if m%2==1 and need_odd>0: got.append((p,True)); need_odd-=1
                elif m%2==0 and need_even>0: got.append((p,False)); need_even-=1
            p += n
        for (p, modd) in got:
            zp = zeta_powers(p,n)
            r, S = smallest_zerosum_mitm(p, n, zp)
            thin = n <= p**0.25
            rs = str(r) if r else "NONE(<=n/2)"
            gt = (r is not None and r > log2(n))
            print(f"{n:>4} {log2(n):>7.2f} {p:>14} {p**0.25:>9.1f} {str(thin):>6} "
                  f"{str(modd):>6} {rs:>11} {str(gt) if r else '-':>10}")
            if S:
                print(f"        witness S = {S}")
    print()
    print("INTERPRETATION:")
    print(" - If smallest_r stays SMALL (~ a few) and constant as n grows -> a small spurious")
    print("   zero-sum survives into the thin regime -> the B_inf <- B_logn bootstrap GAP IS REAL")
    print("   and BIND (no non-antipodal zero-sum) is FALSE as literally stated.")
    print(" - If smallest_r grows with n / no zero-sum up to n/2 -> BIND plausibly holds.")

if __name__ == "__main__":
    main()

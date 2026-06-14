#!/usr/bin/env python3
"""#389 — THE SMOOTH-DOMAIN SUB-JOHNSON LIST SIZE (user directive).

Question: for RS[D, k] with D a MULTIPLICATIVE SUBGROUP (smooth domain, n|q-1),
what is max_w #{codewords at agreement a} in the sub-Johnson range?  k=2 reduces
to max 3-rich lines of a function graph with x-coords in D.

Hypothesis (from the cubic countermodel + Weil): the ADDITIVE worst-case
construction (cubic word, Sylvester Theta(n^2)) is SUPPRESSED on a multiplicative
subgroup to the additive-energy scale ~n^3/q, because a subgroup has few additive
triples (Weil).  So smooth domains have a SUB-QUADRATIC list, unlike additive
(interval) domains.  We measure:
 (A) #additive triples T(D)={a+b+c=0} for subgroup vs interval vs n^3/q.
 (B) max 3-rich lines (hill-climb) for subgroup-domain vs interval-domain words.
 (C) the cubic word x^3 restricted to D: its 3-rich-line count == T(D)?
 (D) exponent of the max list size in n, at fixed q and growing n.
"""
import math, random
from itertools import combinations

def primitive_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    fac = []
    phi = p-1; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    return None

def subgroup(p, n):
    """multiplicative subgroup of order n (requires n | p-1)."""
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # element of order n
    D = []
    x = 1
    for _ in range(n):
        D.append(x); x = (x*h) % p
    return sorted(set(D))

def additive_triples(D, p):
    """#{(a,b,c) in D^3 distinct : a+b+c=0} as unordered 3-subsets."""
    Dset = set(D)
    cnt = 0
    for a, b in combinations(D, 2):
        c = (-(a+b)) % p
        if c in Dset and c != a and c != b and c > b:  # a<b<c ordering via value
            cnt += 1
    return cnt

def rich3_lines(w, dom, p):
    """#lines with >=3 of the |dom| graph points (function graph)."""
    n = len(dom); lines = {}
    for i, j in combinations(range(n), 2):
        dx = (dom[j]-dom[i]) % p
        a = ((w[j]-w[i]) * pow(dx, p-2, p)) % p
        b = (w[i]-a*dom[i]) % p
        lines.setdefault((a,b), set()).update((i,j))
    return sum(1 for s in lines.values() if len(s) >= 3)

def hillclimb_rich3(dom, p, iters, restarts, seed):
    rnd = random.Random(seed); n = len(dom); best = 0
    for r in range(restarts):
        w = [rnd.randrange(p) for _ in range(n)]; cur = rich3_lines(w, dom, p); stale = 0
        for _ in range(iters):
            i = rnd.randrange(n); old = w[i]; w[i] = rnd.randrange(p)
            nv = rich3_lines(w, dom, p)
            if nv >= cur:
                if nv > cur: stale = 0
                cur = nv
            else: w[i] = old; stale += 1
            if stale > 5*n: break
        best = max(best, rich3_lines(w, dom, p))
    return best

print(__doc__)
print("="*72)
print("(A)+(C) additive triples T(D): subgroup vs interval vs n^3/(6q); cubic word check")
# pick primes with many divisors of p-1 for subgroups
cases = [(97,8),(97,12),(97,16),(193,16),(193,24),(769,16),(769,32),(769,48),
         (3079,24),(3079,42),(12289,16),(12289,32),(12289,64)]
for p, n in cases:
    if (p-1) % n: continue
    D = subgroup(p, n)
    Tsub = additive_triples(D, p)
    I = list(range(n))
    Tint = additive_triples(I, p)
    # cubic word on subgroup: w(x)=x^3, count its 3-rich lines (should ~ Tsub-ish)
    wcub = [pow(x,3,p) for x in D]
    cub = rich3_lines(wcub, D, p)
    pred = n**3/(6*p)
    print(f"  p={p:6d} n={n:3d} n/sqrt(q)={n/math.sqrt(p):5.2f} | T(subgrp)={Tsub:4d} "
          f"(n^3/6q={pred:6.1f})  T(interval)={Tint:5d}  cubic_word_rich3={cub:4d}")

print("\n"+"="*72)
print("(B)+(D) MAX 3-rich lines (hill-climb): subgroup-domain vs interval-domain")
for p, n in [(97,12),(97,16),(193,16),(193,24),(769,16),(769,24),(769,32),
             (3079,24),(3079,42),(12289,32),(12289,48)]:
    if (p-1) % n: continue
    D = subgroup(p, n)
    I = list(range(n))
    msub = hillclimb_rich3(D, p, 400, 8, 1)
    mint = hillclimb_rich3(I, p, 400, 8, 1)
    print(f"  p={p:6d} n={n:3d} n/sqrt(q)={n/math.sqrt(p):5.2f} | "
          f"max3rich SUBGROUP={msub:4d} (/n={msub/n:4.2f}, /n^1.5={msub/n**1.5:4.2f}) | "
          f"INTERVAL={mint:4d} (/n={mint/n:4.2f}, /n^2={mint/n**2:.3f})")

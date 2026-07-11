#!/usr/bin/env python3
"""#389 THE SINGLETON STRATUM, directly probed — the localized open core of the wall.

The fold engine (PolynomialFoldDecomposition.lean) folds the FULL-FIBER part of the
supply to half scale. The residual is the SINGLETON stratum: codewords whose agreement
with w is concentrated on antipode-free points (no x,-x both agreeing). This is where any
super-polynomial sub-Johnson supply on prize domains must hide. We measure it directly.

For a word w on mu_n and codewords c (deg<k), split each agreement set A_c by fibers:
  full(c)  = #fibers {x,-x} with both in A_c
  sing(c)  = #points in A_c whose antipode is NOT in A_c (antipode-free)
A codeword is SINGLETON-HEAVY if sing(c) >= full(c)*2 (the fold-irreducible case).
We adversarially MAXIMIZE the number of singleton-heavy codewords with sing(c) >= s,
across the tower n = 8,16,32, sub-Johnson s. If this stays bounded/poly, the open core
is poly => the whole wall is poly on prize domains.

k=2 (lines), direct enumeration. Also report: can we make a word where MANY lines each
have large antipode-free agreement? (the adversary's best singleton attack.)
"""
import sys, math, random
from itertools import combinations
random.seed(389)

def field_prime(n):
    p = max(257, n + 1)
    while True:
        if (p - 1) % n == 0 and all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += 1

def subgroup(p, n):
    m = p-1; fac=set(); d=2; mm=m
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    g=next(g for g in range(2,p) if all(pow(g,m//q,p)!=1 for q in fac))
    h=pow(g,(p-1)//n,p)
    return sorted({pow(h,i,p) for i in range(n)})

def neg_index(dom, p):
    """map i -> index of -dom[i] in dom."""
    pos = {v: i for i, v in enumerate(dom)}
    return [pos[(-dom[i]) % p] for i in range(len(dom))]

def singleton_count(dom, w, p, a, b, negidx):
    """for line a+bx: return (#antipode-free agreements, #full-fiber-pairs)."""
    agree = [ (a + b*dom[i]) % p == w[i] for i in range(len(dom)) ]
    sing = full = 0
    seen = set()
    for i in range(len(dom)):
        if not agree[i]: continue
        j = negidx[i]
        if j == i:  # self-antipodal (x=-x, i.e. x=0 not in subgroup) - skip
            sing += 1; continue
        if agree[j]:
            if i < j: full += 1
        else:
            sing += 1
    return sing, full

def max_singleton_heavy(dom, w, p, s, negidx):
    """#lines with antipode-free agreement >= s AND singleton-heavy."""
    cnt = 0
    seen = set()
    for i, j in combinations(range(len(dom)), 2):
        xi, xj = dom[i], dom[j]
        b = ((w[j]-w[i]) * pow(xj-xi, p-2, p)) % p
        a = (w[i] - b*xi) % p
        if (a,b) in seen: continue
        seen.add((a,b))
        sing, full = singleton_count(dom, w, p, a, b, negidx)
        if sing >= s and sing >= 2*full:
            cnt += 1
    return cnt

def hill(dom, p, s, negidx, iters):
    n = len(dom); best = 0
    for _ in range(4):
        w = [random.randrange(p) for _ in range(n)]
        cur = max_singleton_heavy(dom, w, p, s, negidx)
        for _ in range(iters):
            i = random.randrange(n); old = w[i]
            w[i] = random.randrange(p)
            new = max_singleton_heavy(dom, w, p, s, negidx)
            if new >= cur: cur = new
            else: w[i] = old
        best = max(best, cur)
    return best

print("mu  n   p     s   Johnson  max#singleton-heavy-lines  ratio-to-n", flush=True)
for mu in (3, 4, 5):
    n = 1 << mu
    p = field_prime(n)
    dom = subgroup(p, n)
    negidx = neg_index(dom, p)
    johnson = math.sqrt(2*n)
    s = max(2, round(0.7*johnson))   # sub-Johnson antipode-free agreement
    best = hill(dom, p, s, negidx, 250)
    print(f"{mu}  {n:3d} {p:5d}  {s}   {johnson:.2f}     {best:3d}                      {best/n:.2f}",
          flush=True)
print(flush=True)
print("If max#singleton-heavy stays O(n) [bounded ratio]: the open core is poly => "
      "wall poly on prize domains (delta*=capacity-Theta(1/log n) hypothesis supported).",
      flush=True)
print("If it grows super-linearly with n: the singleton stratum carries the explosion.",
      flush=True)

#!/usr/bin/env python3
"""
Boundary-regime additive-energy probes for #389 (Fable wf2).

Setting: G = mu_n = {x in F_p : x^n = 1}, n | p-1, n = 2^m where possible.
The deployed (closed) regime is p > 2^n: E = 3n^2 - 3n exactly.
The OPEN boundary regime is n ~ sqrt(p). We want to pin E(mu_n) there.

Definitions:
  additive energy E(G) = #{(a,b,c,d) in G^4 : a+b=c+d}
  energy excess    = E(G) - (3n^2 - 3n)   (>= 0 ; = #{F_p-only quadruples})
  rep count   r(t) = #{(a,b) in G^2 : a+b=t}  ; E = sum_t r(t)^2
  zero-sum-triple T = #{(a,b,c): a+b+c=0}

We probe how the excess grows as p decreases toward n^2 (the boundary n ~ sqrt p),
for n = 2^m, and look for:
  (1) the exact E at the boundary (is it ~ n^2 log n, or a clean closed form?)
  (2) whether the EXCESS is governed by a vanishing-4-sum / cyclotomic-resultant count
  (3) the SIGNED-BASIS / 2-adic lattice structure of the excess quadruples
"""
import sympy
from sympy import primerange, isprime
from collections import defaultdict, Counter
import itertools, math

def primitive_root_of_order(p, n):
    """Return an element of multiplicative order n in F_p, or None."""
    assert (p-1) % n == 0
    g = sympy.primitive_root(p)
    return pow(g, (p-1)//n, p)

def mu_n(p, n):
    w = primitive_root_of_order(p, n)
    return set(pow(w, i, p) for i in range(n))

def additive_energy(G, p):
    cnt = Counter()
    Gl = list(G)
    for a in Gl:
        for b in Gl:
            cnt[(a+b) % p] += 1
    return sum(v*v for v in cnt.values()), cnt

def zero_sum_triples(G, p):
    Gs = set(G); t=0
    Gl=list(G)
    for a in Gl:
        for b in Gl:
            if (-(a+b))%p in Gs: t+=1
    return t

def excess_quadruples(G, p):
    """Return list of (a,b,c,d) with a+b=c+d that are NOT in the 'minimal' families.
       Minimal families: {a,b}={c,d} (diagonal, 2n^2-n) and antipodal (b=-a,d=-c, 3n(n-1) extra... )
       We instead just classify ALL quadruples by structure to find the boundary excess."""
    Gl=list(G); Gs=set(G)
    byS=defaultdict(list)
    for a in Gl:
        for b in Gl:
            byS[(a+b)%p].append((a,b))
    return byS

print("="*78)
print("PROBE 1: boundary E(mu_n) for n=2^m as p decreases toward n^2")
print("="*78)
print(f"{'m':>2} {'n':>5} {'p':>8} {'p/n^2':>7} {'E':>9} {'3n2-3n':>8} {'excess':>7} {'E/n^2':>7} {'E/(n^2 ln n)':>12}")
for m in range(2,7):
    n = 2**m
    # collect a range of primes p ≡ 1 mod n, from just above n^2 up to large
    targets = [int(n*n*r) for r in (1.0,1.3,2.0,4.0,16.0,64.0)]
    seen=set()
    for tgt in targets:
        # find prime p ≡ 1 mod n near tgt
        p = ((tgt)//n)*n + 1
        for _ in range(200000):
            if isprime(p) and p>n*n*0.5: break
            p += n
        if p in seen: continue
        seen.add(p)
        G = mu_n(p,n)
        if len(G)!=n: continue
        E,_ = additive_energy(G,p)
        mn = 3*n*n-3*n
        exc = E-mn
        lnn = math.log(n)
        print(f"{m:>2} {n:>5} {p:>8} {p/(n*n):>7.2f} {E:>9} {mn:>8} {exc:>7} {E/(n*n):>7.3f} {E/(n*n*lnn):>12.4f}")
    print()

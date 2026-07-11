#!/usr/bin/env python3
"""
probe_dsj_energy_vs_incidence.py

ADVERSARIAL test of [AC1]: does the additive-energy FLOOR E(mu_n) >= n^2
"force" the far-line incidence threshold s* to the sqrt(rho)*n = n/2 scale?

Setup: mu_n = n-th roots of unity in F_p (n = 2^mu, smooth domain), rho = 1/4,
k = rho*n = n/4 = dimension. A "far line" direction is a degree-k polynomial g;
its incidence with the RS evaluation domain mu_n is the number of x in mu_n with
g(x) on the line (here we test the over-determined worst direction = monomial
readout dir(n/4, 5n/8) per the GPU finding). We want to check:

  (a) Is the GPU formula s*(n) = n/2 + 1 - 2*(log2 n - 3) reproduced by a clean
      char-0 incidence count?  (we re-derive over a large prime as proxy for char 0)
  (b) AC1 mechanism: the energy E = sum_t r(t)^2 where r(t)=#{(a,b) in mu_n^2 : a-b=t}.
      Floor E >= n^2 is TRIVIAL (diagonal t=0 alone gives r(0)=n => n^2).
      Question: does this floor have ANY directional content tying it to s* ?
      We test whether energy of mu_n is ~ n^2 (Sidon, no excess) or has excess
      that scales like s*.

This probe does NOT need the GPU; it checks the LOGICAL link AC1 asserts.
DO NOT git commit.
"""
import sys
from math import log2, isqrt

def find_prime_with_root(n, lo):
    # find prime p > lo with p = 1 mod n (so mu_n exists in F_p)
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p):
            return p
        p += 1

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31):
        if m % q == 0: return m == q
    d = m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True

def primitive_nth_root(p, n):
    # n | p-1; find element of order exactly n
    g = 2
    while True:
        cand = pow(g, (p-1)//n, p)
        # check order is exactly n
        order_ok = all(pow(cand, n//q, p) != 1 for q in prime_factors(n))
        if order_ok:
            return cand
        g += 1

def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f

def mu_set(p, n):
    w = primitive_nth_root(p, n)
    s=[]; cur=1
    for _ in range(n):
        s.append(cur); cur=cur*w%p
    return s

def additive_energy(mu, p):
    # E = #{(a,b,c,d): a+b=c+d} = sum_t r(t)^2, r(t)=#{(a,b):a+b=t}
    from collections import Counter
    cnt = Counter()
    for a in mu:
        for b in mu:
            cnt[(a+b)%p]+=1
    return sum(v*v for v in cnt.values())

def main():
    print("n   p           E(mu_n)      n^2        n^3        E/n^2   E-n^2(excess)")
    for mu in range(3,7):   # n = 8,16,32,64
        n = 2**mu
        p = find_prime_with_root(n, 10**7)  # big prime ~ char-0 proxy
        mu_n = mu_set(p, n)
        E = additive_energy(mu_n, p)
        print(f"{n:<3} {p:<11} {E:<12} {n*n:<10} {n**3:<10} {E/n/n:.3f}  {E-n*n}")
    print()
    print("INTERPRETATION:")
    print("  Sidon set: E = n^2 + (lower order). If E ~ n^2 the floor is just the")
    print("  diagonal and carries NO directional s* info => AC1 link is vacuous.")
    print("  If E has a structured excess ~ c*n^2.something tied to dyadic depth,")
    print("  AC1 might have content. Compare excess column to 2*(mu-3)*n.")
    print()
    print("  GPU formula s*(n) = n/2 + 1 - 2*(log2 n - 3):")
    for mu in range(3,9):
        n=2**mu
        s=n//2+1-2*(mu-3)
        print(f"    n={n:<4} s*={s:<4} m*=s*-n/4={s-n//4:<4} delta*={0.5-1/n+2*(mu-3)/n:.4f}")

if __name__=="__main__":
    main()

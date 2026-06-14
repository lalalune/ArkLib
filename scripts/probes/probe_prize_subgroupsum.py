#!/usr/bin/env python3
"""
Attack the COMMON SINK of survivors R2/N1/S3: the sub-sqrt(q) incomplete
character sum over mu_n. Three independent hypotheses all reduce to bounding
  S(a,j) = | sum_{x in mu_n} e_p(a * x^j) |   (monomial subgroup Gauss sum)
better than the Weil sqrt(p) per frequency, in the prize regime.

Bourgain-Glibichuk-Konyagin / Bourgain-Garaev: for H <= F_p* with |H| > p^delta,
character/exponential sums over H are <= |H|^{1-eps} -- can be SUB-sqrt(p) when
|H| < sqrt(p). The prize regime: p = Theta(n^beta) (polynomial field, KKH26/B3),
so |mu_n| = n = p^{1/beta}. For beta > 2, n < sqrt(p) -- the BGK regime where
sub-sqrt(p) bounds live.

MEASURE max_{a != 0} S(a,j) vs sqrt(p) and vs n, for prize-like (p ~ n^beta):
- if S << sqrt(p) AND small vs the window budget => the technique EXISTS, real
  lead to break the wall.
- if S ~ sqrt(p) or ~ n (trivial) => wall confirmed from the analytic side.
"""
import cmath, math

def find_prime_pow(n, beta):
    # smallest prime p >= n^beta with n | p-1

    target = int(n**beta)
    p = ((target)//n + 1)*n + 1
    while True:
        if p>2 and all(p%d for d in range(2,int(p**0.5)+1)): return p
        p += n

def subgroup(p, n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    return None

def max_monomial_sum(p, H, j, asamp=200):
    n=len(H)
    Hj=[pow(x,j,p) for x in H]
    import random; rng=random.Random(1)
    best=0.0
    A = range(1,p) if p<=400 else [rng.randrange(1,p) for _ in range(asamp)]
    for a in A:
        s=sum(cmath.exp(2j*math.pi*(a*y % p)/p) for y in Hj)
        m=abs(s)
        if m>best: best=m
    return best

print("n  beta  p   |mu_n|=n  sqrt(p) | max_a max_{j<k} |S(a,j)|  ratio/sqrt(p)  ratio/n")
for (n, beta) in [(16,3),(32,3),(64,3),(16,4),(32,4),(64,2.2),(128,2.2)]:
    p=find_prime_pow(n,beta)
    H=subgroup(p,n)
    if H is None: print(f"n={n} beta={beta} p={p}: no subgroup"); continue
    k=3
    best=0.0
    for j in range(1,k+2):  # monomials up to deg k+1 (the supply's range)
        if math.gcd(j,n)!=1 and j>1:  # still measure, just note
            pass
        best=max(best, max_monomial_sum(p,H,j))
    sp=math.sqrt(p)
    print(f"{n:4d} {beta:4} {p:8d}  {n:4d}  {sp:8.1f} | "
          f"maxS={best:8.2f}  /sqrt(p)={best/sp:.3f}  /n={best/n:.3f}  "
          f"{'SUB-sqrt(p)!' if best < 0.95*sp else 'at-Weil'}")

#!/usr/bin/env python3
"""
Johnson-scale list size for k=2 smooth RS, via the rich-line incidence count
(feasible at real n -- O(n^2) per word, NO q^k enumeration).

For k=2, deg<2 codewords are lines q(x)=ax+b; agreement with word w on >=a
points = # lines containing >= a of the n points P = {(x_i, w_i)}. So the
RS list at agreement a IS the count of "a-rich lines" through P. Johnson
agreement for k=2: a_J = ceil(sqrt(2n)). The PRIZE question (is the explicit
smooth-RS list poly STRICTLY beyond Johnson?) becomes: for x_i in mu_n
(dyadic), how many rich lines at a slightly BELOW a_J (just inside the window
1-sqrt(rho))?

This probe: dyadic n up to 256, p chosen with n|p-1; adversarial words w
(structured: agree with subgroup-coset lines) + random; count max rich-line
list at agreement levels around Johnson. Poly growth => prize plausibly
winnable for k=2 (incidence route); super-poly => beyond-Johnson dead.
"""
import math, random
from collections import defaultdict

def find_prime_with_order(n, lo=2):
    # smallest prime p > lo with n | p-1
    c = ((lo)//n + 1)*n + 1
    while True:
        if c > 2 and all(c % d for d in range(2, int(c**0.5)+1)):
            return c
        c += n

def smooth_domain(p, n):
    for cand in range(2, p):
        h = pow(cand, (p-1)//n, p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,j,p) for j in range(n)]
    raise RuntimeError

def rich_lines(D, p, w, a):
    """count lines y=Ax+B through >= a of points (D[i], w[i])."""
    n=len(D); cnt=defaultdict(int)
    # for each pair, the line; but count per line via slope-intercept buckets
    # better: for each ordered pair compute (A,B); a line with m pts counted
    # C(m,2) times -> recover m. Use dict line->set of pts.
    lines=defaultdict(set)
    for i in range(n):
        for j in range(i+1,n):
            dx=(D[i]-D[j])%p
            if dx==0: continue
            A=((w[i]-w[j])*pow(dx,p-2,p))%p
            B=(w[i]-A*D[i])%p
            lines[(A,B)].add(i); lines[(A,B)].add(j)
    return sum(1 for s in lines.values() if len(s)>=a)

random.seed(5)
print("n  p  rho  Johnson_a  | max rich-list at a=J-1, J, J+1 (struct / rand)")
for mu in (4,5,6,7,8):
    n=2**mu
    p=find_prime_with_order(n, 200)
    D=smooth_domain(p,n)
    k=2; aJ=math.ceil(math.sqrt(2*n))
    def structured_w():
        # stitch 2 lines on the two index-parity cosets (subgroup mu_{n/2})
        A1,B1,A2,B2=[random.randrange(p) for _ in range(4)]
        return [ (A1*D[i]+B1)%p if i%2==0 else (A2*D[i]+B2)%p for i in range(n)]
    best={a:0 for a in (aJ-1,aJ,aJ+1)}
    for _ in range(8):
        for w in (structured_w(), [random.randrange(p) for _ in range(n)]):
            for a in (aJ-1,aJ,aJ+1):
                if a>=2: best[a]=max(best[a], rich_lines(D,p,w,a))
    print(f"{n:4d} {p:6d} {k/n:.4f}  J={aJ:3d}  | "
          f"a={aJ-1}:{best[aJ-1]}  a={aJ}:{best[aJ]}  a={aJ+1}:{best[aJ+1]}")

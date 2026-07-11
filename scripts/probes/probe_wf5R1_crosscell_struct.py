#!/usr/bin/env python3
"""
WF5-R1 STRUCTURED FORM: the dyadic descent route to the Wick energy bound.
  E_s(mu_n) = 2 E_s(mu_{n/2}) + crossCell(mu_{n/2}, zeta, 2s).
If Wick(n,s)=(2s-1)!! n^s holds, the diagonal floor 2 E_s(mu_{n/2}) <= 2 Wick(n/2,s) = Wick(n,s)/2^{s-1}.
So Wick(n) holds iff crossCell <= (1 - 2^{1-s}) Wick(n,s).
STRUCTURED SUFFICIENT LEMMA (the sharp form for the dyadic route):
    crossCell(mu_{n/2}, zeta, 2s)  <=  (2^{s-1} - 1) * 2 * E_s(mu_{n/2}).      (***)
This is the CORRECT replacement for the refuted "eps<1" diagonal form: the multiplier is 2^{s-1}-1
(grows with s), NOT eps<1. Test (***) exactly char-0; also test it implies Wick if Wick holds at n/2.
"""
from collections import defaultdict
import sympy
def dfact(k):
    r=1
    while k>0: r*=k; k-=2
    return r
def N0_exact(S,p,r):
    dist={0:1}
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for x in S: nd[(s+x)%p]+=c
        dist=nd
    return dist.get(0,0)
def subgroup(p,n):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[];x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return sorted(set(S))
print("Test (***): crossCell(H,2s) <= (2^{s-1}-1)*2*E_s(H),  G=mu_n, H=mu_{n/2}")
print(f"{'n':>4}{'s':>3}{'E_s(H)':>14}{'cross':>14}{'(2^{s-1}-1)2E':>16}{'ratio':>8}{'holds':>7}")
for mu in [4,5]:  # n=16,32 with H=mu_8,mu_16
    n=2**mu
    p=sympy.nextprime(n**4)
    while (p-1)%n!=0: p=sympy.nextprime(p)
    G=subgroup(p,n); H=subgroup(p,n//2)
    for s in range(2,6):
        r=2*s
        eg=N0_exact(G,p,r); eh=N0_exact(H,p,r)
        cross=eg-2*eh
        bound=(2**(s-1)-1)*2*eh
        ratio=cross/bound if bound>0 else float('nan')
        print(f"{n:>4}{s:>3}{eh:>14}{cross:>14}{bound:>16}{ratio:>8.3f}{('Y' if cross<=bound else 'N'):>7}")
    print()

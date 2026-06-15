#!/usr/bin/env python3
"""Confirm the constraint lemma: the half-coset sum S0(b)=sum_{x in mu_{n/2}} e_p(bx)
is REAL for all b, BECAUSE -1 in mu_{n/2} (mu_{n/2} is a 2-power subgroup of even
order => contains the unique element of order 2 = -1). Reality => cos01(b) in {+1,-1}
trivially. So '|cos01|=1' is NOT a tower law; it's automatic. Verify -1 in mu_{n/2}
and that S0 imaginary part ~ 0."""
import numpy as np
def gen(p):
    fac=set(); x=p-1; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac): g+=1
    return g
def subgroup(p,n):
    g=gen(p); h=pow(g,(p-1)//n,p); return [pow(h,i,p) for i in range(n)]
w=lambda p:-2*np.pi/p
for (p,n) in [(257,8),(1153,16),(12289,32),(40961,64),(257,128),(12289,6144),(786433,32)]:
    H=subgroup(p,n)
    if len(set(H))!=n or n%2: continue
    sq=sorted({(x*x)%p for x in H})        # mu_{n/2}, order n/2
    neg1_in = (p-1) in set(sq)             # is -1 a square here?
    # S0(b) imag parts over sample
    maximag=0.0
    for b in range(1,50):
        S0=sum(np.exp(1j*w(p)*((b*x)%p)) for x in sq)
        maximag=max(maximag,abs(S0.imag))
    print(f"p={p:>7} n={n:>5} |mu_(n/2)|={len(sq):>5} (-1 in mu_(n/2))? {neg1_in}  max|Im S0(b)|={maximag:.2e}")

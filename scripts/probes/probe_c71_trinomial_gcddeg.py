#!/usr/bin/env python3
"""
PROBE v4 (#444 C71 3-term strata): the PROVABLE sharp mechanism.
A root x in mu_n of g(X)=X^{i-k} - c1 X^{j-k} - c2  (dehomogenised trinomial, deg=i-k) is ALSO a
root of X^n - 1. So #{roots in mu_n} <= #{roots of gcd(X^n-1, g)} <= deg gcd(X^n-1, g).
This is the SAME provable mechanism as RepCountFiberGcdSharp (common-root/gcd divisibility),
Mathlib-backed (card_roots_le_degree + gcd divisibility), char-free.
TEST: (i) is the mu_n-incidence <= deg gcd(X^n-1, g)? (ii) how does deg-gcd compare to GCDSUM and i-k?
"""
import itertools, math
from sympy import Poly, gcd, symbols, GF

X=symbols('X')
def subgroup_gen(p,n):
    def order(g):
        x=1
        for e in range(1,p):
            x=(x*g)%p
            if x==1: return e
        return p-1
    for cand in range(2,p):
        if order(cand)==p-1: return pow(cand,(p-1)//n,p)
def main():
    cases=[(97,8),(193,16),(257,16),(521,8)]
    gcddeg_ok=True; tighter_than_deg=0; total=0; gcddeg_eq_count=0
    for (p,n) in cases:
        if (p-1)%n or (p-1)//n<2: continue
        g0=subgroup_gen(p,n); mun=[pow(g0,t,p) for t in range(n)]
        step=max(1,(p-1)//12)
        Xnm1=Poly(X**n-1, X, modulus=p)
        for i,j,k in itertools.combinations(range(n),3):
            i,j,k=max(i,j,k),sorted([i,j,k])[1],min(i,j,k)
            di,dj=i-k,j-k
            for c1 in range(1,p,step):
                for c2 in range(1,p,step):
                    r=sum(1 for x in mun if (pow(x,i,p)-c1*pow(x,j,p)-c2*pow(x,k,p))%p==0)
                    if r==0: continue
                    total+=1
                    gpoly=Poly(X**di - c1*X**dj - c2, X, modulus=p)
                    gd=gcd(Xnm1,gpoly)
                    dg=gd.degree()
                    if r>dg: gcddeg_ok=False
                    if dg < (i-k): tighter_than_deg+=1
                    if r==dg: gcddeg_eq_count+=1
    print(f"(GCDDEG) #roots <= deg gcd(X^n-1, g) : {'HOLDS' if gcddeg_ok else 'FAILS'}")
    print(f"  deg-gcd STRICTLY tighter than deg(g)=i-k in {tighter_than_deg}/{total} nonzero configs")
    print(f"  deg-gcd EXACTLY equals #roots in {gcddeg_eq_count}/{total} configs (sharpness)")
if __name__=="__main__": main()

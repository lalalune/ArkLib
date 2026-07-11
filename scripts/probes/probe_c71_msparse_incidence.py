#!/usr/bin/env python3
"""
PROBE (#444 C71 residual GENERAL-m lift): does the gcd-incidence law
  #{x in mu_n : f(x)=0} <= deg gcd(X^n-1, g)   (g = dehomogenised f, deg = e_max - e_min)
hold and stay SHARP for GENERAL m-sparse directions f = sum_t c_t X^{e_t}, m=2,3,4,5?
This would let a SINGLE general-m theorem subsume binomial(d9615d195)+trinomial(mine).
Strided F_p^* coefficients (SAMPLED, honest). NEVER n=q-1. thin mu_n=2^a.
"""
import itertools, math
from sympy import Poly, gcd, symbols
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
    cases=[(97,8),(193,16),(257,16)]
    for m in (2,3,4):
        gok=True; tighter=0; eq=0; tot=0
        for (p,n) in cases:
            if (p-1)%n or (p-1)//n<2 or m>n: continue
            g0=subgroup_gen(p,n); mun=[pow(g0,t,p) for t in range(n)]
            Xnm1=Poly(X**n-1,X,modulus=p)
            step=max(1,(p-1)//4)
            for exps in itertools.combinations(range(n),m):
                exps=sorted(exps); emin,emax=exps[0],exps[-1]
                # coefficients: c on each term, sampled stride; fix leading=1, vary the rest a bit
                for cs in itertools.product(range(1,p,step),repeat=m-1):
                    coeffs=[1]+list(cs)  # c on exps[0]..; arbitrary nonzero leading
                    def fval(x):
                        return sum(coeffs[t]*pow(x,exps[t],p) for t in range(m))%p
                    r=sum(1 for x in mun if fval(x)==0)
                    if r==0: continue
                    tot+=1
                    # dehomogenise: g = sum coeffs[t] X^{exps[t]-emin}, deg = emax-emin
                    gpoly=Poly(sum(coeffs[t]*X**(exps[t]-emin) for t in range(m)),X,modulus=p)
                    dg=gcd(Xnm1,gpoly).degree()
                    if r>dg: gok=False
                    if dg<(emax-emin): tighter+=1
                    if r==dg: eq+=1
        print(f"m={m}: gcd-incidence HOLDS={gok}  sharp(eq) {eq}/{tot}  tighter-than-(emax-emin) {tighter}/{tot}")
if __name__=="__main__": main()

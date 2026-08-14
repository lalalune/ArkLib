#!/usr/bin/env python3
"""
PROBE v3 (#444 C71 3-term strata): find a PROVABLE mechanism for the trinomial incidence bound.
Candidate decompositions of  R = {x in mu_n : x^i - c1 x^j - c2 x^k = 0}  (i>j>k):
 (A) UNION-OF-BINOMIALS:  R ⊆ {x: x^i = c1 x^j} ∪ {x: x^i = c2 x^k}  ? -- test SUBSET
 (B) DEGREE: |R| <= i-k (proven by card_roots of dehomogenised deg-(i-k) poly) -- always true
 (C) Is R itself a coset / coset-union? check |R| in {0} ∪ {divisors-sum}
We test (A) as a literal subset to see if the union bound is the provable route, else fall back to (B).
"""
import itertools, math
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
    unionA_ok=True; failex=None; checked=0
    for (p,n) in cases:
        if (p-1)%n or (p-1)//n<2: continue
        g=subgroup_gen(p,n); mun=[pow(g,t,p) for t in range(n)]
        step=max(1,(p-1)//30)
        for i,j,k in itertools.combinations(range(n),3):
            i,j,k=max(i,j,k),sorted([i,j,k])[1],min(i,j,k)
            for c1 in range(1,p,step):
                for c2 in range(1,p,step):
                    R=set(x for x in mun if (pow(x,i,p)-c1*pow(x,j,p)-c2*pow(x,k,p))%p==0)
                    if not R: continue
                    checked+=1
                    # (A) is each root in one of the two pairwise binomial sets?
                    B1=set(x for x in mun if (pow(x,i,p)-c1*pow(x,j,p))%p==0) # x^i=c1 x^j
                    B2=set(x for x in mun if (pow(x,i,p)-c2*pow(x,k,p))%p==0) # x^i=c2 x^k
                    if not R.issubset(B1|B2):
                        unionA_ok=False
                        if failex is None: failex=(p,n,i,j,k,c1,c2,sorted(R),sorted(B1|B2))
    print(f"(A) UNION-OF-BINOMIALS R ⊆ B1∪B2 : {'HOLDS' if unionA_ok else 'FAILS'}  (checked {checked} nonzero-R configs)")
    if failex: print("  FAIL EX:", failex)
if __name__=="__main__": main()

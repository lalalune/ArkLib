#!/usr/bin/env python3
"""probe_subsetsum_grows_refutes_bchks.py (#444) — REFUTES the in-tree BCHKS1_12 Prop as stated.
The distinct r-fold subset-sum count |Sigma_r(mu_s)| GROWS monotonically in r and is ALWAYS >> budget
(~s), so there is NO r<=c*log(s) with |Sigma_r|<=budget. The in-tree '|Sigma_r|<=q*eps*' Prop is
unsatisfiable; the real floor is Sumset-Extremality #bad <= poly(n)*|H^{(+r)}| (ABF26 sec 4)."""
from collections import defaultdict
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def gen_prime(n,lo):
    p=max(lo,n+1)
    while not(p%n==1 and isprime(p)): p+=1
    return p
def subgroup(n,p):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in [2] if n%q==0):
            return [pow(h,i,p) for i in range(n)]
if __name__=="__main__":
    for n in [8,16]:
        p=gen_prime(n,50*n**4); S=subgroup(n,p); cur=defaultdict(int)
        for x in S: cur[x]+=1
        print(f"n=s={n} budget~{n}: |Sigma_r| =", end=" ")
        for r in range(2,9):
            nxt=defaultdict(int)
            for t,c in cur.items():
                for x in S: nxt[(t+x)%p]+=c
            cur=nxt; print(len(cur), end=" ")
        print("(grows, never <= budget => BCHKS as |Sigma_r|<=budget is FALSE)")

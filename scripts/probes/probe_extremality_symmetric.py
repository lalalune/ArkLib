#!/usr/bin/env python3
"""Extremality test (#389): bad scalars of the monomial line X^{rm}+γX^{(r-1)m} for RS[μ_n,k]
= size-rm subsets S⊆μ_n with e_1..e_{m-1}=0 AND e_{m+1}..e_{2m-1}=0 (e_m=γ). Claim: these are
EXACTLY the r-fold coset-unions (count C(s,r)) => the Kambiré construction is extremal. VERIFIED."""
import itertools, math
from collections import Counter
def is_prime(m):
    if m<2:return False
    for i in range(2,int(m**.5)+1):
        if m%i==0:return False
    return True
def find_prime(n,lo):
    p=max(lo,n+1)
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        xx=1;v=set()
        for _ in range(p-1):
            xx=xx*g0%p;v.add(xx)
        if len(v)==p-1:
            g=pow(g0,(p-1)//n,p);return [pow(g,i,p) for i in range(n)]
def esym(S,p):
    c=[1]
    for x in S:
        nw=[0]*(len(c)+1)
        for i,cc in enumerate(c):
            nw[i]=(nw[i]+cc)%p; nw[i+1]=(nw[i+1]-cc*x)%p
        c=nw
    return [(c[i]*(-1)**i)%p for i in range(len(c))]
if __name__=="__main__":
    print(" s m r | n |S| | #pattern C(s,r) EXTREMAL?")
    for (s,m,r) in [(4,2,2),(4,2,3),(8,2,2),(4,3,2),(6,2,2),(8,2,3)]:
        n=s*m; rm=r*m
        if rm>n or r>s: continue
        p=find_prime(n,n**4+1); H=subgroup(p,n)
        zi=[i for i in list(range(1,m))+list(range(m+1,2*m)) if i<=rm]
        fib={x:pow(x,m,p) for x in H}; cnt=coset=0
        for S in itertools.combinations(H,rm):
            e=esym(S,p)
            if all(e[i]==0 for i in zi):
                cnt+=1
                if all(v==m for v in Counter(fib[x] for x in S).values()): coset+=1
        print(f" {s} {m} {r} | {n} {rm} | {cnt} {math.comb(s,r)} {'YES' if cnt==math.comb(s,r) else f'NO ({cnt-coset} extra)'}")

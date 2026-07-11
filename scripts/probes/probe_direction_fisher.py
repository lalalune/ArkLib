#!/usr/bin/env python3
"""Direction-Fisher bound (#389): for ANY stack (u0,u1), #{bad gamma at agreement a} < (a-b)n/(a^2-bn)
where b=max-agreement(u1,C). Proof: two bad gammas g,g' => on S_g∩S_g', (g-g')u1=c_g-c_g' is a
codeword => |S_g∩S_g'| <= b; Fisher/Jensen. No character sums. VERIFIED + tight for the construction.
Reach: vacuous when a^2<=bn => recovers Johnson radius only (pairwise wall)."""
import itertools, math, random
random.seed(3)
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
def max_agree(p,H,w,k):
    n=len(H);best=0
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub];ys=[w[i] for i in sub];ag=0
        for j in range(n):
            X=H[j];fx=0
            for i in range(k):
                num=ys[i]%p;den=1
                for l in range(k):
                    if l==i:continue
                    num=num*((X-xs[l])%p)%p;den=den*((xs[i]-xs[l])%p)%p
                fx=(fx+num*pow(den,p-2,p))%p
            if fx==w[j]:ag+=1
        best=max(best,ag)
    return best
def bad_count(p,H,u0,u1,k,A):
    return sum(1 for g in range(p) if max_agree(p,H,[(u0[i]+g*u1[i])%p for i in range(len(H))],k)>=A)
if __name__=="__main__":
    s,m,r=4,2,3;n=s*m;k=(r-2)*m+1;a=r*m;p=find_prime(n,n**4+1);H=subgroup(p,n)
    for desc,u0,u1 in [("monomial",[pow(x,6,p) for x in H],[pow(x,4,p) for x in H])]+\
                       [("random",[random.randrange(p) for _ in range(n)],[random.randrange(p) for _ in range(n)]) for _ in range(4)]:
        b=max_agree(p,H,u1,k);bc=bad_count(p,H,u0,u1,k,a);d=a*a-b*n
        fb='vac' if d<=0 else f'{(a-b)*n/d:.1f}'
        print(f"{desc:9s} b={b} #bad={bc} Fisher={fb}")

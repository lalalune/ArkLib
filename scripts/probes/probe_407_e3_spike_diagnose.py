from collections import Counter
import itertools
def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def subgroup(p,n):
    for cand in range(2,p):
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(cand,i,p) for i in range(n)]
p=32993; n=32
G=subgroup(p,n)
# what's the additive structure? count N(t) = #{pairs (a,b) in G^2 : a+b=t}, look for big collisions
N2=Counter()
for a in G:
    for b in G:
        N2[(a+b)%p]+=1
# E_2 additive energy
E2=sum(v*v for v in N2.values())
print(f"p={p} n={n}: E2={E2} (Sidon/random E2~2n^2-n={2*n*n-n}, neg-closed adds n^2 DC at t=0)")
print(f" N2[0]={N2[0]} (DC, = #(a,b): a+b=0 = n if -1 in G)")
mx=max((v,t) for t,v in N2.items() if t!=0)
print(f" max off-zero N2: {mx[0]} at t={mx[1]} (random=2)")
# is p special? p-1 factorization
def factor(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
print(f" p-1 = {p-1} = {factor(p-1)}")
print(f" p   = {p} factor check prime, p mod 32 = {p%32}, (p-1)/32 = {(p-1)//32} = {factor((p-1)//32)}")
# count how many off-zero t have N2>2 (additive resonances)
res=sum(1 for t,v in N2.items() if t!=0 and v>2)
print(f" #off-zero t with N2>2 (3-term arithmetic resonances): {res}")

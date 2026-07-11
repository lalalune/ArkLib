# Verify: #explainable (k+m+1)-cores of w = Σ_c C(|A_c|, k+m+1), sum over codewords c
# with |agreement(c,w)| >= k+m+1. (Each core belongs to exactly one codeword.)
from itertools import product, combinations
from math import comb
import random

def codewords(Fq,n,k,dom):
    return [tuple(sum(c[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for c in product(range(Fq),repeat=k)]

def explainable_cores(cw,n,a,w):
    cores=set()
    for c in cw:
        ag=[i for i in range(n) if c[i]==w[i]]
        if len(ag)>=a:
            for T in combinations(ag,a): cores.add(T)
    return len(cores)

def sum_formula(cw,n,a,w):
    tot=0
    for c in cw:
        agc=sum(1 for i in range(n) if c[i]==w[i])
        if agc>=a: tot+=comb(agc,a)
    return tot

random.seed(3); ok=True
for (Fq,n,k) in [(5,5,2),(7,6,2),(7,7,3),(11,8,2)]:
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    for m in range(0,3):
        a=k+m+1
        if a>n: continue
        for _ in range(25):
            w=tuple(random.randrange(Fq) for _ in range(n))
            lhs=explainable_cores(cw,n,a,w)
            rhs=sum_formula(cw,n,a,w)
            if lhs!=rhs:
                ok=False; print(f"MISMATCH F{Fq} n{n} k{k} m{m}: {lhs} vs {rhs}")
print("EXACT IDENTITY HOLDS (all random words, all params):", ok)

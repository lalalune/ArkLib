"""
A8 final confirmation: the affine-group gap collapses with p (amenability is STRUCTURAL,
not a small-p artifact). Fix n=8, sweep p (PRIME, n|p-1, proper subgroup). A genuine
Bourgain-Gamburd expander family would have gap BOUNDED BELOW uniformly in p. We show it -> 0.
"""
import numpy as np, math
from sympy import isprime, primitive_root
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

def gen_h(p,n):
    g=primitive_root(p); return pow(g,(p-1)//n,p)

def affine_gap(p,h,n):
    N=n*p
    hpow=[pow(h,s,p) for s in range(n)]
    def idx(s,c): return s*p+c
    rows=[];cols=[]
    for s in range(n):
        for c in range(p):
            i=idx(s,c)
            for j in (idx((s+1)%n,c),idx((s-1)%n,c),idx(s,(c+hpow[s])%p),idx(s,(c-hpow[s])%p)):
                rows.append(i);cols.append(j)
    A=sp.coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(N,N)).tocsr(); A=(A+A.T)/2
    vals=np.sort(eigsh(A,k=6,which='LA')[0])[::-1]
    return vals[0]-vals[1]

n=8
print(f"n={n} fixed, sweeping PRIME p with n|p-1 (proper subgroup). BG would need gap bounded below.")
print(f"{'p':>6} {'|Aff|':>7} {'gap':>9}")
ps=[]
k=2
while len(ps)<6:
    p=k*n+1
    if isprime(p) and n*p<=12000:
        ps.append(p)
    k+=1
    if k*n+1 > 1500: break
for p in ps:
    h=gen_h(p,n); g=affine_gap(p,h,n)
    print(f"{p:>6} {n*p:>7} {g:>9.5f}")
print("If gap -> 0 with p, the family is NOT an expander => NO Bourgain-Gamburd gap (amenable).")

import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

def primitive_root_mod_p(p):
    if p==2:return 1
    phi=p-1;mm=phi;d=2;fac=[]
    while d*d<=mm:
        if mm%d==0:
            fac.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fac.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):return g
def find_thin_prime(n,lo):
    t=(lo-1)//n+1
    while True:
        p=1+n*t
        if isprime(p):return p
        t+=1

def solve_gamma_for_subset(p,n,k,b,sub,powers):
    rows=[];rhs=[]
    for j in sub:
        xj=powers[j]
        row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,k,p))%p]
        rows.append(row);rhs.append(pow(xj,b,p)%p)
    M=[rows[i][:]+[rhs[i]] for i in range(len(rows))]
    rows_n=len(M);cols=k+1
    Mr=[[x%p for x in r] for r in M];r=0;pivcol=[]
    for col in range(cols):
        piv=None
        for i in range(r,rows_n):
            if Mr[i][col]%p!=0:piv=i;break
        if piv is None: continue
        Mr[r],Mr[piv]=Mr[piv],Mr[r];inv=pow(Mr[r][col],p-2,p);Mr[r]=[(x*inv)%p for x in Mr[r]]
        for i in range(rows_n):
            if i!=r and Mr[i][col]%p!=0:
                f=Mr[i][col];Mr[i]=[(Mr[i][jj]-f*Mr[r][jj])%p for jj in range(cols+1)]
        pivcol.append(col);r+=1
        if r==rows_n:break
    for i in range(r,rows_n):
        if Mr[i][cols]%p!=0: return ('incons',None)
    if k in pivcol:
        ri=pivcol.index(k);rowk=Mr[ri];free=[c for c in range(cols) if c not in pivcol]
        if any(rowk[c]%p!=0 for c in free): return ('free',None)
        return ('det', rowk[cols]%p)
    else:
        return ('free',None)

def bad_scalars_at_w(p,n,k,b,g,w):
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    bad=set();free=False
    if comb(n,w)>2_000_000: return None
    for sub in combinations(range(n),w):
        kind,val=solve_gamma_for_subset(p,n,k,b,sub,powers)
        if kind=='det':bad.add(val)
        elif kind=='free':free=True
    return len(bad),free

print("=== bad-scalar count SWEEP over w (find delta* = first w where #bad jumps), char-p ===")
print("Monomial line, low-exp far dir b. Tracks #bad vs n (BGK) or const (off-BGK).")
for n in [8,12,16]:
    p=find_thin_prime(n,3000);g=primitive_root_mod_p(p);k=max(2,n//4)
    b=k+1
    print(f"--- n={n} k={k} b={b} p={p}  budget=n={n}, sqrt(nk)={sqrt(n*k):.1f} ---")
    print("   w   delta   #bad  free?")
    for w in range(n-1, k, -1):
        res=bad_scalars_at_w(p,n,k,b,g,w)
        if res is None: print(f"  {w:2d}  (too big)"); continue
        nb,free=res
        print(f"  {w:2d}  {1-w/n:.3f}  {nb:4d}  {free}")

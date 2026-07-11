import numpy as np
from math import sqrt, log

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def v2(x):
    k=0
    while x%2==0:x//=2;k+=1
    return k
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def M_of(p,roots):
    rr=np.array(roots,dtype=np.int64); M=0.0; BL=8000
    for i in range(1,p,BL):
        bb=np.arange(i,min(i+BL,p),dtype=np.int64)[:,None]
        ph=np.exp(2j*np.pi*((bb*rr[None,:])%p)/p).sum(axis=1)
        M=max(M,float(np.abs(ph).max()))
    return M
def find_prime(target, n, maxv2=False):
    # prime p ~ target with n|p-1; if maxv2, maximize v2(p-1)
    best=None; bestv=-1
    lo=max(n+1, target-target//8); hi=target+target//8
    cnt=0
    p=lo - (lo % n) + 1
    while p<hi and cnt< (400 if maxv2 else 1):
        if (p-1)%n==0 and is_prime(p):
            vv=v2(p-1)
            if maxv2:
                if vv>bestv: bestv=vv; best=p
                cnt+=1
            else:
                return p
        p+=n
    return best

print("DISPROVE search: worst-case C(n)=M/sqrt(n log(p/n)) — maximal-v2 (structured) vs generic prize prime")
print("drift UP ⟹ disproof signal; SATURATE ⟹ conjecture TRUE")
print("="*72)
for mu in (4,5,6):
    n=2**mu; target=n**4
    pg=find_prime(target,n,maxv2=False)
    pm=find_prime(target,n,maxv2=True)
    rows=[]
    for tag,p in (("generic",pg),("max-v2",pm)):
        if p is None: continue
        roots=subgroup(p,n); M=M_of(p,roots)
        C=M/sqrt(n*log(p/n)); Cs=M/sqrt(n*log(p))
        rows.append((tag,p,v2(p-1),M,C,Cs))
    print(f"\nn={n} (p~n^4=2^{4*mu}):")
    for tag,p,vv,M,C,Cs in rows:
        print(f"  {tag:8s} p={p:11d} v2={vv:2d}: M={M:8.2f}  C=M/sqrt(n log(p/n))={C:.4f}  M/sqrt(n log p)={Cs:.4f}")

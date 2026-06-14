import numpy as np, itertools, math
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)):return g
def matinv(A,p):
    n=A.shape[0];M=np.concatenate([A%p,np.eye(n,dtype=np.int64)],1)%p
    for c in range(n):
        piv=next((r for r in range(c,n) if M[r,c]%p),None)
        if piv is None:return None
        M[[c,piv]]=M[[piv,c]];M[c]=(M[c]*pow(int(M[c,c]),p-2,p))%p
        for r in range(n):
            if r!=c and M[r,c]%p:M[r]=(M[r]-M[r,c]*M[c])%p
    return M[:,n:]%p
def prof(n,k,p):
    g=proot(p);h=pow(g,(p-1)//n,p)
    pts=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    V=np.ones((n,k),dtype=np.int64)
    for j in range(1,k):V[:,j]=(V[:,j-1]*pts)%p
    mats=[(list(S),(V@matinv(V[list(S),:],p))%p) for S in itertools.combinations(range(n),k)
          if matinv(V[list(S),:],p) is not None]
    pw=np.ones((n,n),dtype=np.int64)
    for a in range(1,n):pw[a]=(pw[a-1]*pts)%p
    al=np.arange(p,dtype=np.int64);P={w:0 for w in range(k+1,n+1)}
    for a in range(k,n):
        for b in range(k,n):
            if a==b:continue
            Vw=(pw[a][None,:]+np.outer(al,pw[b]))%p;best=np.zeros(p,dtype=np.int64)
            for S,M in mats: np.maximum(best,((Vw[:,S]@M.T)%p==Vw).sum(1),out=best)
            for w in P:
                c=int((best>=w).sum())
                if c>P[w]:P[w]=c
    return P
print("margin trend (budget - J at last good band) across n, fixed small k:",flush=True)
for n,k in [(8,2),(16,2),(32,2),(16,3)]:
    p=int(n**4)|1
    while not(isprime(p) and (p-1)%n==0):p+=1
    P=prof(n,k,p);budget=n;ws=sorted(P)
    thr=next((w for w in ws if P[w]<=budget),None)
    zero=next((w for w in ws if P[w]==0),None)
    sp=" ".join(f"{w}:{P[w]}" for w in ws if P[w]>0)
    print(f"n={n} k={k} p={p}: {sp} | budget={budget} w*={thr}(J={P.get(thr)}) zero@{zero} width={zero-thr if thr and zero else None} margin={budget-P[thr] if thr else None}",flush=True)
print("DONE",flush=True)

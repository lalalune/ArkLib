import itertools, random
import numpy as np
random.seed(9); np.random.seed(9)
def subgroup(p,n):
    e=(p-1)//n
    for b in range(2,p):
        g=pow(b,e,p)
        if g!=1 and pow(g,n//2,p)!=1:
            G=[];x=1
            for _ in range(n):G.append(x);x=x*g%p
            if len(set(G))==n:return G
    return None
def maxlist(p,dom,k,t,starts=25,iters=70):
    n=len(dom)
    polys=np.array(list(itertools.product(range(p),repeat=k)))
    pw=np.array([[pow(a,j,p) for j in range(k)] for a in dom])
    vals=((polys@pw.T)%p).astype(np.int16)
    def L(w): return int((((vals==w).sum(1))>=t).sum())
    best=0
    for _ in range(starts):
        w=np.random.randint(0,p,n).astype(np.int16); b=L(w)
        for _ in range(iters):
            i=random.randrange(n); bv=w[i]; bb=b
            for val in range(p):
                w[i]=val; c=L(w)
                if c>bb: bb=c; bv=val
            w[i]=bv; b=bb
        best=max(best,b)
    return best
# n=8 t=3 across proper fields (confirm field-independence = 7 = n-1?)
print("n=8,k=2,t=3 (proper mu_8):")
for p in [17,41,73,89,97,113,137,193,233,257]:
    if (p-1)%8: continue
    d=subgroup(p,8)
    if d: print(f"  p={p}: maxlist={maxlist(p,d,2,3)}", flush=True)

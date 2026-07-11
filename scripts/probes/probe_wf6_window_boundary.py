# probe_wf6_window_boundary.py (Target A4, Fable) -- the load-bearing measurement
# Confirms: maxbad(a) is a q-INDEPENDENT CONSTANT for a >= k+2, and Theta(q) at a=k+1.
# This pins delta* and is the basis of the SURVIVING conjecture (C-window).
import itertools, random, sys
from math import comb
def pf(n):
    f=set();d=2;m=n
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def gen(p,n):
    for a in range(2,p):
        if pow(a,n,p)==1 and all(pow(a,n//q,p)!=1 for q in pf(n)):return a
def lag(xs,ys,k,p):
    m=k;A=[[pow(xs[i],j,p) for j in range(m)]+[ys[i]] for i in range(m)]
    for col in range(m):
        piv=next((r for r in range(col,m) if A[r][col]%p),None)
        if piv is None:return None
        A[col],A[piv]=A[piv],A[col];inv=pow(A[col][col],p-2,p)
        A[col]=[(v*inv)%p for v in A[col]]
        for r in range(m):
            if r!=col and A[r][col]%p:
                f=A[r][col];A[r]=[(A[r][t]-f*A[col][t])%p for t in range(m+1)]
    return [A[i][m]%p for i in range(m)]
def ev(c,x,p):
    r=0
    for cc in reversed(c):r=(r*x+cc)%p
    return r%p
def expl(L,dom,k,p,a):
    n=len(dom);seen={};out=[]
    for T in itertools.combinations(range(n),a):
        c=lag([dom[i] for i in T][:k],[L[i] for i in T][:k],k,p)
        if c is None:continue
        if not all(ev(c,dom[i],p)==L[i] for i in T):continue
        key=tuple(c)
        if key in seen:continue
        seen[key]=1;out.append(frozenset(i for i in range(n) if ev(c,dom[i],p)==L[i]))
    return out
def joint(S,u0,u1,dom,k,p):
    Sl=sorted(S)
    if len(Sl)<k:return True
    def ok(u):
        c=lag([dom[i] for i in Sl[:k]],[u[i] for i in Sl[:k]],k,p)
        if c is None:return False
        return all(ev(c,dom[i],p)==u[i] for i in Sl)
    return ok(u0) and ok(u1)
def mca_bad(u0,u1,dom,k,p,a):
    n=len(dom);c=0
    for g in range(p):
        L=tuple((u0[i]+g*u1[i])%p for i in range(n));fired=False
        for S in expl(L,dom,k,p,a):
            if not joint(S,u0,u1,dom,k,p):fired=True;break
            if len(S)>a:
                Sl=sorted(S);d=False
                for Sp in itertools.combinations(Sl,a):
                    if not joint(frozenset(Sp),u0,u1,dom,k,p):d=True;break
                if d:fired=True;break
        if fired:c+=1
    return c
def maxbad(p,n,k,a,ns,seed):
    g=gen(p,n);dom=[pow(g,j,p) for j in range(n)];random.seed(seed);best=0
    S=[(tuple(random.randrange(p) for _ in range(n)),tuple(random.randrange(p) for _ in range(n))) for _ in range(ns)]
    for e0 in range(k,n):
        for e1 in range(k,n):
            S.append((tuple(pow(x,e0,p) for x in dom),tuple(pow(x,e1,p) for x in dom)))
    for (u0,u1) in S:best=max(best,mca_bad(u0,u1,dom,k,p,a))
    return best
n,k=8,2
primes=[17,41,73,89,97,113]
print(f"n={n} k={k} rho={k/n} johnson_delta={1-(k/n)**0.5:.3f} capacity_delta={1-k/n:.3f}");sys.stdout.flush()
for a in [6,5,4,3]:
    row=[maxbad(p,n,k,a,120,1) for p in primes]
    delta=1-a/n;const=len(set(row))==1
    print(f"a={a} delta={delta:.3f} band(a-k={a-k}): maxbad{primes}={row}  "
          f"{'q-CONSTANT' if const else 'q-DEPENDENT(~Theta q)'}");sys.stdout.flush()

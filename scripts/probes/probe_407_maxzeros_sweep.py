#!/usr/bin/env python3
"""probe_407_maxzeros_sweep.py  (#444: EXACT max-zeros, SWEEPING the far-line direction (a,b))

Reconciles my exact rank computation with the engine's s*~√(kn): the engine MAXIMIZES over far-line
directions (a,b). The previous probe fixed (a,b)=(k+1,k+2)=lowest exponents and got s*=k+2 CONSTANT.
Here we sweep ALL valid (a,b) with k<=a<b<n and report the MAX s* over directions -- the true engine
object -- to see if/where it reaches Johnson, and which directions bind.

Exact rank characterization (same as before): for spectral support T={0..k-1,a,b}, s* over a fixed
direction = max |Z| with rank([w^{tz}]_{z in Z, t in T}) < |T|=K, computed exactly via all (K-1)-subsets.
We then MAX over (a,b).
"""
import itertools, math

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_prime(n, beta):
    target=int(round(n**beta)); p=target-(target%n)+1
    if p<=n+1: p+=n
    for _ in range(500000):
        if (p-1)%n==0 and (p-1)//n>=2 and isprime(p): return p
        p+=n
    return None

def rou(p,n):
    g=2
    while g<p:
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return h
        g+=1
    return None

def solve_null(M, p):
    rows=[r[:] for r in M]; R=len(rows); K=len(rows[0])
    where=[-1]*K; pr=0
    for col in range(K):
        piv=None
        for r in range(pr,R):
            if rows[r][col]%p!=0: piv=r;break
        if piv is None: continue
        rows[pr],rows[piv]=rows[piv],rows[pr]
        inv=pow(rows[pr][col],p-2,p)
        rows[pr]=[(v*inv)%p for v in rows[pr]]
        for r in range(R):
            if r!=pr and rows[r][col]%p!=0:
                f=rows[r][col]; rows[r]=[(rows[r][c]-f*rows[pr][c])%p for c in range(K)]
        where[col]=pr; pr+=1
        if pr==R: break
    free=[c for c in range(K) if where[c]==-1]
    if not free: return None
    fc=free[0]; c=[0]*K; c[fc]=1
    for col in range(K):
        if where[col]!=-1: c[col]=(-rows[where[col]][fc])%p
    return c

def max_zeros_dir(n, p, w, T, cap=400000):
    K=len(T)
    Mfull=[[pow(w,(t*z)%n,p) for t in T] for z in range(n)]
    best=0; cnt=0
    for A in itertools.combinations(range(n), K-1):
        cnt+=1
        if cnt>cap: break
        c=solve_null([Mfull[z] for z in A],p)
        if c is None: continue
        zeros=sum(1 for z in range(n) if sum(Mfull[z][j]*c[j] for j in range(K))%p==0)
        if zeros>best: best=zeros
    return best

if __name__=="__main__":
    print("=== EXACT max-zeros s*, MAX over far-line directions (a,b) -- the engine object ===")
    print("(proper mu_n, prize-band p, m>=2, never n=q-1; band T={0..k-1}, sweep k<=a<b<n)\n")
    beta=4.0; k=3
    band=list(range(k))
    print(f"k={k}, K=k+2=5. Johnson=√(kn). Reporting MAX s* over directions + the binding (a,b).")
    print(f"{'n':>4} {'p':>10} {'maxs*':>6} {'s*-k':>5} {'Johnson':>8} {'bind(a,b)':>10} "
          f"{'#dirs@max':>9}")
    for n in [8, 16, 32]:
        p=find_prime(n,beta); w=rou(p,n)
        best=0; binders=[]; 
        for a in range(k, n):
            for b in range(a+1, n):
                cap = 400000 if n<=16 else 120000
                s=max_zeros_dir(n,p,w,band+[a,b],cap=cap)
                if s>best: best=s; binders=[(a,b)]
                elif s==best: binders.append((a,b))
        john=math.sqrt(k*n)
        print(f"{n:>4} {p:>10} {best:>6} {best-k:>5} {john:>8.2f} {str(binders[0]):>10} {len(binders):>9}")
        print(f"      all binding dirs (s*={best}): {binders[:12]}{'...' if len(binders)>12 else ''}")

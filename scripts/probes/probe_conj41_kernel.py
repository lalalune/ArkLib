#!/usr/bin/env python3
"""
Conj 41 rigorous rank/kernel test + diagnostic of the line-M_true overcount.
A genuine line with m supports compatible at distinct gamma_i <=> (s1,s2) in ker(A),
A = stack[N_Ei | gamma_i N_Ei] (mc x 2D). For m=2D/c (square A): kernel exists iff det(A)=0.
det(A) is a polynomial of degree <= c in each gamma_i, so its roots are findable EXACTLY at any p.
We then check whether the kernel line gives GENUINE (all-nonzero) weight-w errors for all m supports
(true M_true>=m) or a DEGENERATE one (escape). Distinguishes a real large-p counterexample from a bug.
"""
import itertools, functools, random
print = functools.partial(print, flush=True)

def poly_from_roots(roots, p):
    c=[1]
    for r in roots:
        nc=[0]*(len(c)+1)
        for i,a in enumerate(c):
            nc[i]=(nc[i]-r*a)%p; nc[i+1]=(nc[i+1]+a)%p
        c=nc
    return c
def normals(E,L,D,c,p):
    lam=poly_from_roots([L[e] for e in E],p); rows=[]
    for r in range(c):
        row=[0]*D
        for i,a in enumerate(lam):
            if i+r<D: row[i+r]=a%p
        rows.append(row)
    return rows
def vander(E,L,D,p): return [[pow(L[e],j,p) for e in E] for j in range(D)]
def detmod(M,p):
    M=[r[:] for r in M]; n=len(M); det=1
    for c in range(n):
        piv=next((i for i in range(c,n) if M[i][c]%p!=0),None)
        if piv is None: return 0
        if piv!=c: M[c],M[piv]=M[piv],M[c]; det=(-det)%p
        det=(det*M[c][c])%p; inv=pow(M[c][c]%p,p-2,p)
        for i in range(c+1,n):
            if M[i][c]%p!=0:
                f=(M[i][c]*inv)%p; M[i]=[(M[i][j]-f*M[c][j])%p for j in range(n)]
    return det%p
def kernel_vec(M,p):
    """one nonzero kernel vector of square M (assumes rank=n-1), else None."""
    n=len(M); A=[r[:] for r in M]; where=[-1]*n; pr=0
    for c in range(n):
        piv=next((i for i in range(pr,n) if A[i][c]%p!=0),None)
        if piv is None: continue
        A[pr],A[piv]=A[piv],A[pr]; inv=pow(A[pr][c]%p,p-2,p); A[pr]=[(x*inv)%p for x in A[pr]]
        for i in range(n):
            if i!=pr and A[i][c]%p!=0:
                f=A[i][c]%p; A[i]=[(A[i][j]-f*A[pr][j])%p for j in range(n)]
        where[c]=pr; pr+=1
    free=[c for c in range(n) if where[c]==-1]
    if not free: return None
    fc=free[0]; x=[0]*n; x[fc]=1
    for c in range(n):
        if where[c]!=-1: x[c]=(-A[where[c]][fc])%p
    return x
def build_A(Es,gammas,L,D,c,p):
    A=[]
    for E,g in zip(Es,gammas):
        N=normals(E,L,D,c,p)
        for row in N: A.append([x%p for x in row]+[(g*x)%p for x in row])  # [N | g N], width 2D
    return A
def solve_unique(V,s,p):
    D=len(V); w=len(V[0]); A=[V[i][:]+[s[i]] for i in range(D)]; pr=0; where=[-1]*w
    for col in range(w):
        piv=next((i for i in range(pr,D) if A[i][col]%p!=0),None)
        if piv is None: return None
        A[pr],A[piv]=A[piv],A[pr]; inv=pow(A[pr][col]%p,p-2,p); A[pr]=[(x*inv)%p for x in A[pr]]
        for i in range(D):
            if i!=pr and A[i][col]%p!=0:
                f=A[i][col]%p; A[i]=[(A[i][j]-f*A[pr][j])%p for j in range(w+1)]
        where[col]=pr; pr+=1
    for i in range(pr,D):
        if A[i][w]%p!=0: return None
    v=[0]*w
    for col in range(w): v[col]=A[where[col]][w]%p
    return v

def det_as_poly_in_last_gamma(Es,g_fixed,L,D,c,p):
    """det(A) as polynomial in gamma_m (degree<=c); return coeffs via interpolation at c+1 points."""
    deg=c; xs=list(range(deg+1)); ys=[]
    for gv in xs:
        A=build_A(Es,list(g_fixed)+[gv],L,D,c,p)
        ys.append(detmod(A,p))
    # Lagrange interpolation -> coefficient at the unique poly deg<=c (over F_p)
    # Newton / solve Vandermonde:
    M=[[pow(xs[i],j,p) for j in range(deg+1)] for i in range(deg+1)]
    # solve M coef = ys
    Aug=[M[i][:]+[ys[i]] for i in range(deg+1)]; n=deg+1; where=[-1]*n; pr=0
    for col in range(n):
        piv=next((i for i in range(pr,n) if Aug[i][col]%p!=0),None)
        if piv is None: continue
        Aug[pr],Aug[piv]=Aug[piv],Aug[pr]; inv=pow(Aug[pr][col]%p,p-2,p); Aug[pr]=[(x*inv)%p for x in Aug[pr]]
        for i in range(n):
            if i!=pr and Aug[i][col]%p!=0:
                f=Aug[i][col]%p; Aug[i]=[(Aug[i][j]-f*Aug[pr][j])%p for j in range(n+1)]
        where[col]=pr; pr+=1
    coef=[0]*n
    for col in range(n):
        if where[col]!=-1: coef[col]=Aug[where[col]][n]%p
    return coef  # low->high
def poly_roots(coef,p):
    return [x for x in range(p) if sum(coef[j]*pow(x,j,p) for j in range(len(coef)))%p==0]

def genuine_Mtrue_clique(clique,n,k,p,L=None,trials=200,seed=1):
    """For the (w+1)-clique, find distinct-gamma configs with det(A)=0 and check if the kernel line gives
       all-nonzero weight-w errors for all m=w+1 supports (=> GENUINE M_true>=w+1). Return (#genuine, example)."""
    D=n-k; 
    if L is None: L=list(range(n))
    Es=[tuple(sorted(set(clique)-{a})) for a in clique]
    w=len(Es[0]); c=D-w
    m=len(Es)
    if m*c!=2*D:  # need square A for det-root method
        return ('skip(m*c!=2D)',None)
    rng=random.Random(seed); genuine=0; ex=None
    for _ in range(trials):
        gf=rng.sample(range(1,p),m-1)
        if len(set(gf))<m-1: continue
        coef=det_as_poly_in_last_gamma(Es,gf,L,D,c,p)
        for gm in poly_roots(coef,p):
            if gm in gf: continue   # need distinct
            gammas=gf+[gm]
            A=build_A(Es,gammas,L,D,c,p)
            kv=kernel_vec(A,p)
            if kv is None: continue
            s1=kv[:D]; s2=kv[D:]
            if all(x%p==0 for x in s1) and all(x%p==0 for x in s2): continue
            # require s1, s2 linearly independent (genuine 2-dim line, not a degenerate ray)
            def lin_dep(a,b,pp):
                # true if a,b parallel over F_pp
                ia=next((i for i in range(len(a)) if a[i]%pp!=0),None)
                ib=next((i for i in range(len(b)) if b[i]%pp!=0),None)
                if ia is None or ib is None: return True
                if ia!=ib: return False
                lam=(b[ib]*pow(a[ia],pp-2,pp))%pp
                return all((b[t]-lam*a[t])%pp==0 for t in range(len(a)))
            if lin_dep(s1,s2,p): continue
            ok=True
            for E,g in zip(Es,gammas):
                N=normals(E,L,D,c,p)
                Ns2=[sum(N[i][j]*s2[j] for j in range(D))%p for i in range(c)]
                if all(x%p==0 for x in Ns2): ok=False; break   # ESCAPE: support compatible with whole line (not an isolated gamma)
                s=[(s1[j]+g*s2[j])%p for j in range(D)]
                v=solve_unique(vander(E,L,D,p),s,p)
                if v is None or any(x%p==0 for x in v): ok=False; break
            if ok:
                genuine+=1; ex=(gammas,s1,s2)
                break
    return (genuine,ex)

print("=== Conj41 rank/kernel: tetrahedron clique {1,4,5,8}, n=12,k=6 (w=3,c=3,D=6,2D=12,mc=12) ===")
n,k=12,6; clique=[1,4,5,8]; D=n-k; w=3; c=3; bound=(2*D-1)//c
print(f"   bound floor((2D-1)/c) = {bound};  m=w+1=4 would VIOLATE if genuine")
for p in [61, 1009, 10007, 100003, 1000003]:
    g,ex=genuine_Mtrue_clique(clique,n,k,p,trials=120,seed=2)
    tag = "GENUINE m=4 EXISTS (>bound)" if isinstance(g,int) and g>0 else ("none found" if g==0 else g)
    print(f"   p={p:>8}: #configs with genuine all-nonzero M_true>=4 found = {g}   [{tag}]")

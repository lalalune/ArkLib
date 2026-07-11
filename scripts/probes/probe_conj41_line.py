#!/usr/bin/env python3
"""
Conj 41 (Open-Set Rank Lemma, c>=3 line version) of ePrint 2026/858.
Line list size M_true(s1,s2) = #{distinct gamma : exists w-subset E decodable at s1+gamma*s2 with a
genuine nonzero weight-w error}. Prize bound: max M_true(s1,s2) <= floor((2D-1)/c), D=n-k, w=D-c.
Reproduce the c=3 tetrahedron counterexample at p=61, show it VANISHES at large p, extend to rate 1/2.
"""
import itertools, random, functools
print = functools.partial(print, flush=True)

def poly_from_roots(roots, p):
    """coeffs (low->high) of prod (x-r); length len(roots)+1."""
    c = [1]
    for r in roots:
        nc = [0]*(len(c)+1)
        for i,a in enumerate(c):
            nc[i]   = (nc[i]   - r*a) % p   # -r * a x^i
            nc[i+1] = (nc[i+1] + a) % p     # a x^{i+1}
        c = nc
    return c

def normals(E, L, D, c, p):
    """c x D matrix: rows = coeff vectors (len D) of Lambda_E(x)*x^r, r=0..c-1."""
    lam = poly_from_roots([L[e] for e in E], p)   # length w+1 = D-c+1
    rows = []
    for r in range(c):
        row = [0]*D
        for i,a in enumerate(lam):
            if i+r < D: row[i+r] = a % p
        rows.append(row)
    return rows

def vander(E, L, D, p):
    return [[pow(L[e], j, p) for e in E] for j in range(D)]   # D x w

def solve_unique(V, s, p):
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

def mv(M, x, p):  # M (rows) times vector x
    return [sum(M[i][j]*x[j] for j in range(len(x)))%p for i in range(len(M))]

def gamma_for(E, L, D, c, p, s1, s2):
    """unique compatibility gamma for support E on line s1+gamma s2 (or None / 'all')."""
    N=normals(E,L,D,c,p); a=mv(N,s1,p); b=mv(N,s2,p); g=None
    for i in range(c):
        if b[i]%p==0:
            if a[i]%p!=0: return None
        else:
            gi=(-a[i]*pow(b[i],p-2,p))%p
            if g is None: g=gi
            elif g!=gi: return None
    return ('all' if g is None else g)

def line_Mtrue(s1, s2, n, k, w, p, L, subs=None):
    D=n-k; c=D-w
    if subs is None: subs=list(itertools.combinations(range(n),w))
    good=set()
    for E in subs:
        g=gamma_for(E,L,D,c,p,s1,s2)
        if g is None: continue
        if g=='all':                      # degenerate: skip (whole line compatible — escape case)
            continue
        s=[(s1[j]+g*s2[j])%p for j in range(D)]
        v=solve_unique(vander(E,L,D,p), s, p)
        if v is not None and all(x%p!=0 for x in v):
            good.add(g)
    return len(good)

def clique_max_Mtrue(n, k, w, clique, p, L, trials=4000, seed=1):
    """Search lines through pairs of decodable clique-support syndromes; return max line_Mtrue found."""
    D=n-k; c=D-w
    Es=[tuple(sorted(set(clique)-{a})) for a in clique]   # the |clique| supports = clique minus one pt
    Es=[E for E in Es if len(E)==w]
    subs=list(itertools.combinations(range(n),w))
    rng=random.Random(seed); best=0; bestline=None
    for _ in range(trials):
        Ei,Ej=rng.sample(Es,2) if len(Es)>=2 else (Es[0],Es[0])
        vi=[rng.randrange(1,p) for _ in range(w)]; vj=[rng.randrange(1,p) for _ in range(w)]
        sa=mv(vander(Ei,L,D,p),vi,p); sb=mv(vander(Ej,L,D,p),vj,p)
        s1=sa; s2=[(sb[t]-sa[t])%p for t in range(D)]
        if all(x%p==0 for x in s2): continue
        m=line_Mtrue(s1,s2,n,k,w,p,L,subs)
        if m>best: best=m; bestline=(s1,s2)
    return best

print("=== (A) c=3 TETRAHEDRON counterexample (n=12,k=6,w=3,c=3): clique {1,4,5,8}; bound floor((2D-1)/c)=floor(11/3)=3 ===")
n,k,w=12,6,3; D=n-k; c=D-w; bound=(2*D-1)//c
clique=[1,4,5,8]
for p in [61, 1009, 10007, 100003]:
    L=list(range(n))
    if p<=max(L): continue
    m=clique_max_Mtrue(n,k,w,clique,p,L,trials=6000,seed=3)
    print(f"  p={p:>7}: max line-M_true over clique {clique} = {m}   bound={bound}   {'VIOLATES (>bound)' if m>bound else 'within bound'}")

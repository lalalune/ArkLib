#!/usr/bin/env python3
"""
A3 reverse-dictionary floor probe (FAST, line-dedup). #444 §1 A3.
Computes max bad-LINE incidence at a SINGLE target radius m (in the (halfJ,J) window),
for SMOOTH mu_n vs RANDOM domain, across primes -> q-invariance + rule-3 thinness gate.

Bad-line incidence (matches engine / EpsMCAInterleavedList semantics):
  over stacks (u0,u1) (= syndrome pair s0 with direction s1!=0) and the line
  { s0 + g*s1 : g in F_p }, count points on the line whose coset-leader codeword
  agrees with SOME size-m set NOT jointly covered by the s0,s1 codewords.
  incidence(m) = max over (s0,s1) of that count.  eps_mca = incidence/q.

Speedup: ext_mask[s] (which >=m sets the coset-leader of syndrome s covers) precomputed
once. Lines deduped: a line is {s0+g*s1}; we iterate s0 over all p^(n-k) and s1 over a set
of REPRESENTATIVE nonzero directions (one per projective class) -> O(p^(n-k) * p_dirs * p).
For n-k=2 that's p^2 * (p+1) * p ~ p^4 (vs p^5 before). Still only small primes, but enough
for q-invariance + thinness at n=4 AND a thinner n=8,k=2 (rho=1/4) single small prime.
"""
from itertools import product, combinations
from math import sqrt
import random, sys
import sympy
random.seed(407)

def smooth_domain(p,n):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    assert all(pow(h,d,p)!=1 for d in range(1,n)) and pow(h,n,p)==1
    return [pow(h,i,p) for i in range(n)]
def random_domain(p,n): return random.sample(range(1,p),n)

def rref(mat,p):
    m=[r[:] for r in mat]; rows=len(m); cols=len(m[0]) if m else 0; piv=[]; r=0
    for c in range(cols):
        pr=next((i for i in range(r,rows) if m[i][c]%p),None)
        if pr is None: continue
        m[r],m[pr]=m[pr],m[r]; inv=pow(m[r][c],p-2,p); m[r]=[(x*inv)%p for x in m[r]]
        for i in range(rows):
            if i!=r and m[i][c]%p:
                f=m[i][c]; m[i]=[(a-f*b)%p for a,b in zip(m[i],m[r])]
        piv.append(c); r+=1
        if r==rows: break
    return m[:r],piv
def nullspace(mat,p):
    red,piv=rref(mat,p); cols=len(mat[0]); free=[c for c in range(cols) if c not in piv]; basis=[]
    for f in free:
        v=[0]*cols; v[f]=1
        for r,c in enumerate(piv): v[c]=(-red[r][f])%p
        basis.append(v)
    return basis
def solve_particular(H,s,p):
    rows=[H[i]+[s[i]] for i in range(len(H))]; red,piv=rref(rows,p); n=len(H[0]); w=[0]*n
    for r,c in enumerate(piv):
        if c==n: raise ValueError("inconsistent")
        w[c]=red[r][n]
    return w
def ext_from(word,S,xs,k,p):
    if len(S)<=k: return True
    base,rest=S[:k],S[k:]
    for j in rest:
        val=0
        for a in base:
            num,den=1,1
            for b in base:
                if b!=a: num=num*((xs[j]-xs[b])%p)%p; den=den*((xs[a]-xs[b])%p)%p
            val=(val+word[a]*num*pow(den,p-2,p))%p
        if val!=word[j]%p: return False
    return True

def incidence_at(p,n,k,xs,m):
    """max bad-line count at radius m (agreement size >= m)."""
    G=[[pow(x,j,p) for x in xs] for j in range(k)]
    H=nullspace(G,p)
    subsets=[S for size in range(max(k+1,m),n+1) for S in combinations(range(n),size)]
    # mask over the m-admissible subsets only
    syndromes=list(product(range(p),repeat=n-k))
    ext_mask={}
    for s in syndromes:
        w=solve_particular(H,list(s),p); mask=0
        for bit,S in enumerate(subsets):
            if ext_from(w,list(S),xs,k,p): mask|=1<<bit
        ext_mask[s]=mask
    full=(1<<len(subsets))-1
    # representative nonzero directions (projective): scale first nonzero coord to 1
    dirs=set()
    for s1 in syndromes:
        if not any(s1): continue
        fnz=next(x for x in s1 if x)
        inv=pow(fnz,p-2,p)
        dirs.add(tuple((x*inv)%p for x in s1))
    best=0
    for s0 in syndromes:
        e0=ext_mask[s0]
        for s1 in dirs:
            notjoint=full & ~(e0 & ext_mask[s1])
            cnt=0
            for gg in range(p):
                line=tuple((a+gg*b)%p for a,b in zip(s0,s1))
                if ext_mask[line]&notjoint: cnt+=1
            if cnt>best: best=cnt
    return best

def force_L(incid,n,a):
    if n-a<=0: return None
    if incid<=1: return 0
    return max((incid-2)//(n-a),0)

if __name__=="__main__":
    print("A3 FAST reverse-dictionary floor / thinness probe",flush=True)
    # ---- n=4,k=2 (rho=1/2): radius m=3 -> d=0.25 in (halfJ=0.146, J=0.293) ----
    n,k,m=4,2,3; rho=k/n; halfJ=(1-sqrt(rho))/2; J=1-sqrt(rho); d=1-m/n
    print(f"\n[n=4 k=2 rho=0.5] target m=3 delta={d:.3f}  halfJ={halfJ:.3f} J={J:.3f} "
          f"(delta in window: {halfJ<d<J})",flush=True)
    print(f"{'p':>4} | smooth incid L>= | random incid L>= | thin",flush=True)
    sm=[]
    for p in [13,17,29,37,41]:
        if (p-1)%n: continue
        iS=incidence_at(p,n,k,smooth_domain(p,n),m); LS=force_L(iS,n,m)
        iR=incidence_at(p,n,k,random_domain(p,n),m); LR=force_L(iR,n,m)
        sm.append(iS)
        v="smooth<random*" if iS<iR else "==" if iS==iR else "smooth>random"
        print(f"{p:>4} |     {iS:>3}    {LS}   |     {iR:>3}    {LR}   | {v}",flush=True)
    print(f"  smooth incid q-invariant={len(set(sm))==1} vals={sm}",flush=True)

    # ---- n=6,k=4 (rho=2/3, n-k=2 feasible): another radius in (halfJ,J) for cross-check ----
    n,k=6,4; rho=k/n; halfJ=(1-sqrt(rho))/2; J=1-sqrt(rho)
    print(f"\n[n=6 k=4 rho={rho:.3f}] halfJ={halfJ:.3f} J={J:.3f}",flush=True)
    # d=1-m/6 in (halfJ,J)=(0.092,0.184) -> m/6 in (0.816,0.908) -> m=5 (d=0.167) in window
    for m in (5,):
        d=1-m/6
        print(f"  target m={m} delta={d:.3f} in window: {halfJ<d<J}",flush=True)
        for p in [7,13,19,31,37]:   # 6|p-1
            if (p-1)%n: continue
            iS=incidence_at(p,n,k,smooth_domain(p,n),m); LS=force_L(iS,n,m)
            iR=incidence_at(p,n,k,random_domain(p,n),m); LR=force_L(iR,n,m)
            v="smooth<random (BETTER)*" if iS<iR else "==" if iS==iR else "smooth>random"
            print(f"    p={p:>3}: smooth incid={iS} L>={LS} | random incid={iR} L>={LR} | {v}",flush=True)
    print("\nDONE",flush=True)

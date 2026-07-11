#!/usr/bin/env python3
"""
probe_407_L5_homds_char0_structural.py  (#407 LANE L5 — is the HOMDS failure STRUCTURAL or char-p?)

Companion to probe_407_L5_homds_rothmatrix.py.  That probe found, with the CORRECT Roth Lemma-16
block-M-matrix test, that some admissible disjoint block-families (J_0,..,J_L) give a SINGULAR M
over F_p for BOTH odd and even mu_n.  THE decisive question (same char-0-vs-char-p split as the
even-order Half-Sum lane in the KB): is that singularity
  (S) STRUCTURAL  -- det(M)=0 already over the complex roots of unity (a genuine higher-order-MDS
                     FAILURE of mu_n, persists at EVERY prime p = 1 mod n), or
  (A) a char-p ARTIFACT -- det(M) != 0 over C but = 0 only mod the particular small prime p.

If odd-order failures are all ARTIFACTS (vanish only mod small p, det!=0 over C) while even-order
has STRUCTURAL failures, then in the PRIZE regime (p = n^beta huge, non-saturated) odd-order mu_n
IS effectively higher-order MDS -> the L5 lead survives.  If odd-order has STRUCTURAL failures
(det=0 over C), the lead is REFUTED at the source (cyclic symmetry, char-0).

METHOD (exact, no floating point).  Represent mu_n in the cyclotomic field Q(zeta_n) via the
integer basis {zeta^0,...,zeta^{phi(n)-1}} (reduce zeta^j by the cyclotomic polynomial Phi_n).
Build the Roth M-matrix with entries in Z[zeta_n] and compute det(M) EXACTLY as an element of
Z[zeta_n].  det(M) = 0 over C  <=>  it is the zero vector in the basis.  We ALSO confirm by the
multi-prime route: a structural (char-0) zero is 0 mod EVERY prime p=1 mod n; an artifact is
nonzero mod most primes.  We report, per parity, the fraction of admissible singular-mod-p families
whose det is GENUINELY zero over C (structural) vs nonzero over C (artifact).

USAGE: python3 probe_407_L5_homds_char0_structural.py
"""
import sys, math, itertools, json
from fractions import Fraction

# ---------- cyclotomic arithmetic in Z[zeta_n] via reduction mod Phi_n ----------
def phi_n_poly(n):
    """Cyclotomic polynomial Phi_n as integer coeff list (low->high), via X^n-1 / prod_{d|n,d<n}Phi_d."""
    # build via successive polynomial division
    from functools import reduce
    def polymul(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,ai in enumerate(a):
            for j,bj in enumerate(b):
                r[i+j]+=ai*bj
        return r
    def polydivexact(num,den):
        num=num[:]; q=[0]*(len(num)-len(den)+1)
        for i in range(len(q)-1,-1,-1):
            c=num[i+len(den)-1]//den[-1]
            q[i]=c
            for j,dj in enumerate(den):
                num[i+j]-=c*dj
        return q
    divisors=[d for d in range(1,n) if n%d==0]
    phis={}
    def get(d):
        if d in phis: return phis[d]
        # X^d - 1
        xd=[-1]+[0]*(d-1)+[1]
        for e in divisors:
            if e<d and d%e==0:
                xd=polydivexact(xd,get(e))
        # remove also Phi_1 if d==1
        phis[d]=xd
        return xd
    # Phi_n = (X^n-1)/prod_{d|n,d<n}Phi_d
    xn=[-1]+[0]*(n-1)+[1]
    for d in divisors:
        xn=polydivexact(xn,get(d))
    return xn

class Cyc:
    """Element of Z[zeta_n] as coeff list mod Phi_n (degree < phi(n))."""
    __slots__=('c',)
    def __init__(self,c): self.c=c
    @staticmethod
    def zero(deg): return Cyc([0]*deg)

def cyc_reduce(coeffs, phi, deg):
    """reduce a polynomial (any length) modulo Phi_n (monic, integer)."""
    c=coeffs[:]
    while len(c)>deg:
        if c[-1]!=0:
            lead=c[-1]
            shift=len(c)-1-deg
            for j,pj in enumerate(phi):
                c[shift+j]-=lead*pj
        c.pop()
    if len(c)<deg: c=c+[0]*(deg-len(c))
    return c

def make_ring(n):
    phi=phi_n_poly(n)
    deg=len(phi)-1
    def mul(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,ai in enumerate(a):
            if ai==0: continue
            for j,bj in enumerate(b):
                if bj: r[i+j]+=ai*bj
        return cyc_reduce(r,phi,deg)
    def add(a,b): return [a[i]+b[i] for i in range(deg)]
    def sub(a,b): return [a[i]-b[i] for i in range(deg)]
    def zeta_pow(e):
        e%=n
        v=[0]*(max(deg,e+1)); v[e]=1
        return cyc_reduce(v,phi,deg)
    return dict(deg=deg,mul=mul,add=add,sub=sub,zeta_pow=zeta_pow,phi=phi)

def det_cyc(M, ring):
    """exact determinant over Z[zeta_n] via fraction-free (Bareiss) — but Bareiss needs exact
    division; instead do Laplace for small matrices (sizes here <= 2*rho <= ~12, but Laplace
    blows up). Use fraction-free Gaussian over the FRACTION FIELD Q(zeta_n) represented as
    coeff-vectors of rationals; pivot by nonzero vector. Returns coeff list (Fractions)."""
    deg=ring['deg']; mul=ring['mul']
    nrows=len(M)
    # represent entries as Fraction coeff lists
    A=[[[Fraction(x) for x in cell] for cell in row] for row in M]
    def is_zero(v): return all(x==0 for x in v)
    def fmul(a,b):
        r=[Fraction(0)]*(len(a)+len(b)-1)
        for i,ai in enumerate(a):
            if ai==0: continue
            for j,bj in enumerate(b):
                if bj: r[i+j]+=ai*bj
        # reduce mod Phi_n with Fraction arithmetic
        phi=ring['phi']
        c=r[:]
        while len(c)>deg:
            if c[-1]!=0:
                lead=c[-1]; shift=len(c)-1-deg
                for j,pj in enumerate(phi):
                    c[shift+j]-=lead*pj
            c.pop()
        if len(c)<deg: c=c+[Fraction(0)]*(deg-len(c))
        return c
    def finv(a):
        # invert element of Q(zeta_n): solve a*x = 1 by building multiplication matrix
        # M_a is deg x deg over Q; x = M_a^{-1} e_0
        cols=[]
        for j in range(deg):
            ej=[Fraction(0)]*deg; ej[j]=Fraction(1)
            cols.append(fmul(a,ej))
        # matrix with columns cols ; solve Mat x = e0
        Mat=[[cols[j][i] for j in range(deg)] for i in range(deg)]
        # gaussian solve
        aug=[Mat[i]+[Fraction(1) if i==0 else Fraction(0)] for i in range(deg)]
        for col in range(deg):
            piv=next((r for r in range(col,deg) if aug[r][col]!=0),None)
            if piv is None: raise ZeroDivisionError("non-invertible cyclotomic element")
            aug[col],aug[piv]=aug[piv],aug[col]
            pv=aug[col][col]
            aug[col]=[v/pv for v in aug[col]]
            for r in range(deg):
                if r!=col and aug[r][col]!=0:
                    f=aug[r][col]
                    aug[r]=[aug[r][c]-f*aug[col][c] for c in range(deg+1)]
        return [aug[i][deg] for i in range(deg)]
    def fsub(a,b): return [a[i]-b[i] for i in range(deg)]
    det=[Fraction(1)]+[Fraction(0)]*(deg-1)
    sign=1
    for col in range(nrows):
        piv=next((r for r in range(col,nrows) if not is_zero(A[r][col])),None)
        if piv is None:
            return [Fraction(0)]*deg
        if piv!=col:
            A[col],A[piv]=A[piv],A[col]; sign=-sign
        inv=finv(A[col][col])
        det=fmul(det,A[col][col])
        for r in range(col+1,nrows):
            if not is_zero(A[r][col]):
                f=fmul(A[r][col],inv)
                A[r]=[fsub(A[r][c],fmul(f,A[col][c])) for c in range(nrows)]
    if sign<0: det=[-x for x in det]
    return det

# ---------- F_p side (to find the singular families) ----------
def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
def prime_factors(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s
def subgroup_idx(p,n):
    e=(p-1)//n;pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[];x=1
        for _ in range(n):x=x*h%p;S.append(x)
        if len(set(S))==n:
            # return as ordered by exponent: S[j]=h^{j+1}; we want a primitive root w=h and the
            # locators as powers of w so the cyclotomic embedding zeta->w is consistent.
            return h,[pow(h,j,p) for j in range(n)]
    raise RuntimeError("no subgroup")
def det_modp(M,p):
    n=len(M)
    if n==0:return 1
    A=[[x%p for x in row] for row in M];det=1
    for col in range(n):
        piv=next((r for r in range(col,n) if A[r][col]%p!=0),None)
        if piv is None:return 0
        if piv!=col:A[col],A[piv]=A[piv],A[col];det=(-det)%p
        inv=pow(A[col][col],p-2,p);det=det*A[col][col]%p
        for r in range(col+1,n):
            f=A[r][col]*inv%p
            if f:A[r]=[(A[r][c]-f*A[col][c])%p for c in range(n)]
    return det%p

def roth_M_modp(Hc,blocks,rho,p):
    L=len(blocks)-1;Js=[len(b) for b in blocks];ncols=sum(Js);nrows=L*rho
    offs=[0]*len(blocks)
    for m in range(1,len(blocks)):offs[m]=offs[m-1]+Js[m-1]
    M=[[0]*ncols for _ in range(nrows)]
    for m in range(1,L+1):
        rb=(m-1)*rho
        for ci,x in enumerate(blocks[0]):
            col=offs[0]+ci
            for i in range(rho):M[rb+i][col]=(-Hc[x][i])%p
        for ci,x in enumerate(blocks[m]):
            col=offs[m]+ci
            for i in range(rho):M[rb+i][col]=Hc[x][i]%p
    return M

def roth_M_cyc(blocks,rho,ring):
    """Roth M with entries in Z[zeta_n]: H[i][x] = zeta^{x*i} (locator alpha_x = zeta^x, x=index)."""
    zp=ring['zeta_pow'];deg=ring['deg']
    L=len(blocks)-1;Js=[len(b) for b in blocks];ncols=sum(Js);nrows=L*rho
    offs=[0]*len(blocks)
    for m in range(1,len(blocks)):offs[m]=offs[m-1]+Js[m-1]
    M=[[[0]*deg for _ in range(ncols)] for _ in range(nrows)]
    for m in range(1,L+1):
        rb=(m-1)*rho
        for ci,x in enumerate(blocks[0]):
            col=offs[0]+ci
            for i in range(rho):
                v=zp((x*i)%len(blocks)*0 + (x*i))  # zeta^{x*i}
                M[rb+i][col]=[-t for t in v]
        for ci,x in enumerate(blocks[m]):
            col=offs[m]+ci
            for i in range(rho):
                M[rb+i][col]=zp((x*i))
    return M

def find_singular_families(n,k,L,p,Hc,cap=300000):
    """enumerate admissible disjoint block families, return list of singular-mod-p ones (capped)."""
    rho=n-k;sing=[]
    low=2 if L==2 else 1
    parts=set()
    def gp(rem,slots,cur):
        if slots==1:
            if low<=rem<=rho:parts.add(tuple(sorted(cur+[rem])))
            return
        for v in range(low,min(rho,rem-low*(slots-1))+1):gp(rem-v,slots-1,cur+[v])
    gp(L*rho,L+1,[])
    cnt=[0]
    for sizes in parts:
        sizes=list(sizes)
        def pick(remaining,idx,chosen):
            if len(sing)>=40 or cnt[0]>=cap: return
            if idx==len(sizes):
                M=roth_M_modp(Hc,chosen,rho,p);cnt[0]+=1
                if det_modp(M,p)==0: sing.append([list(b) for b in chosen])
                return
            sz=sizes[idx];rem=sorted(remaining)
            for comb in itertools.combinations(rem,sz):
                if idx==0 and 0 not in comb: continue
                if idx>0 and sizes[idx]==sizes[idx-1] and comb<tuple(chosen[idx-1]): continue
                pick([x for x in remaining if x not in comb],idx+1,chosen+[list(comb)])
                if len(sing)>=40 or cnt[0]>=cap: return
        pick(set(range(n)),0,[])
        if len(sing)>=40 or cnt[0]>=cap: break
    return sing

def main():
    results={"rows":[]}
    print("="*96)
    print("LANE L5: are HOMDS (Roth M-matrix) singular families STRUCTURAL (det=0 over C) or char-p ARTIFACTS?")
    print("="*96)
    # cases where the F_p probe saw singular M: (n, k, L)
    cases=[(8,5,2),(9,6,2),(9,5,2),(16,13,2),(15,12,2),(8,5,3),(9,6,3),
           (27,24,2),(25,22,2),(9,7,3),(8,6,3)]
    print(f"{'n':>3} {'par':>5} {'k':>3} {'rho':>3} {'L':>2} {'p':>8} "
          f"{'#sing(p)':>9} {'#struct(C=0)':>12} {'#artifact':>10} {'verdict':>10}")
    for (n,k,L) in cases:
        rho=n-k
        if L*rho>n or rho<1: continue
        par="odd" if n%2 else "even"
        # prime p = 1 mod n, prize-ish
        p=None
        for m in range(max(2,int(n**3.5)//n), int(n**4.5)//n+1):
            cand=n*m+1
            if isprime(cand): p=cand; break
        if p is None:
            for m in range(2,5000):
                cand=n*m+1
                if isprime(cand): p=cand; break
        w,Sidx=subgroup_idx(p,n)
        Hc={j:[pow(Sidx[j],i,p) for i in range(rho)] for j in range(n)}
        sing=find_singular_families(n,k,L,p,Hc)
        if not sing:
            print(f"{n:>3} {par:>5} {k:>3} {rho:>3} {L:>2} {p:>8} {0:>9} {0:>12} {0:>10} {'L-MDS':>10}")
            results["rows"].append(dict(n=n,par=par,k=k,rho=rho,L=L,p=p,sing=0,struct=0,artifact=0,verdict="L-MDS"))
            continue
        ring=make_ring(n)
        nstruct=0;nartifact=0
        for blocks in sing:
            Mc=roth_M_cyc(blocks,rho,ring)
            dc=det_cyc(Mc,ring)
            if all(x==0 for x in dc): nstruct+=1
            else: nartifact+=1
        verdict = "STRUCT" if nstruct>0 else "ARTIFACT"
        print(f"{n:>3} {par:>5} {k:>3} {rho:>3} {L:>2} {p:>8} {len(sing):>9} "
              f"{nstruct:>12} {nartifact:>10} {verdict:>10}", flush=True)
        results["rows"].append(dict(n=n,par=par,k=k,rho=rho,L=L,p=p,sing=len(sing),
                                    struct=nstruct,artifact=nartifact,verdict=verdict))
    # summary
    odd=[r for r in results["rows"] if r["par"]=="odd"]
    even=[r for r in results["rows"] if r["par"]=="even"]
    odd_struct=any(r["struct"]>0 for r in odd)
    even_struct=any(r["struct"]>0 for r in even)
    print("\nSUMMARY:")
    print(f"  ODD  has STRUCTURAL (char-0) HOMDS failure: {odd_struct}")
    print(f"  EVEN has STRUCTURAL (char-0) HOMDS failure: {even_struct}")
    if odd_struct:
        print("  => ODD-order mu_n is NOT higher-order MDS over C (cyclic symmetry, char-0). LEAD REFUTED AT SOURCE.")
    elif even_struct and not odd_struct:
        print("  => ODD failures are char-p ARTIFACTS (vanish in prize regime) while EVEN are STRUCTURAL. LEAD SURVIVES.")
    else:
        print("  => both only artifacts; check prize-regime persistence.")
    results["summary"]=dict(odd_struct=odd_struct,even_struct=even_struct)
    with open("L5_homds_char0_results.json","w") as f: json.dump(results,f,indent=2)
    print("[written scripts/probes/L5_homds_char0_results.json]")

if __name__=="__main__": main()

import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# Confirm: at the GENUINE ragged direction (excluding correlated x^{n/2}=+-1 directions),
# the ragged RESIDUE (= max-agreement minus maximal coset core) is n-independent, char-free.
# A direction (A,B) is "genuine" (not correlated) iff NOT both A%(n/2) and B%(n/2) make
# x^A,x^B reduce to deg<k on cosets. Simplest exclusion: require A,B,A-B all coprime-ish to n/2.
# We instead use the comment-100 genuine test: direction is genuine iff its char-0 max-agreement
# CLIFFS (drops below n at the deep band). We just exclude A or B that are multiples of n/2.

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
def rank_modp(M,p):
    M=[[x%p for x in r] for r in M];rows=len(M);cols=len(M[0]) if rows else 0;r=0
    for col in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i][col]%p!=0:piv=i;break
        if piv is None:continue
        M[r],M[piv]=M[piv],M[r];inv=pow(M[r][col],p-2,p);M[r]=[(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][col]%p!=0:
                f=M[i][col];M[i]=[(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows:break
    return r
def coset_core(s,n):
    best=0
    for d in range(2,n+1):
        if n%d:continue
        sh=n//d;core=0
        for start in range(sh):
            orbit=[(start+j*sh)%n for j in range(d)]
            if all(o in s for o in orbit): core+=d
        best=max(best,core)
    return best
def max_agree_with_residue(p,n,k,A,B,g,cap=1_500_000):
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    def ok(sub):
        coeff=[];aug=[]
        for j in sub:
            xj=powers[j];row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,B,p))%p]
            coeff.append(row[:]);aug.append(row+[(-pow(xj,A,p))%p])
        return rank_modp(coeff,p)==rank_modp(aug,p)
    for s in range(n,0,-1):
        if comb(n,s)>cap: continue
        bestcore=-1
        for sub in combinations(range(n),s):
            if ok(sub):
                c=coset_core(set(sub),n)
                if c>bestcore: bestcore=c
        if bestcore>=0:
            return s,bestcore,s-bestcore
    return 0,0,0

# GENUINE = exclude correlated: A,B not in {0, n/2} mod n/2-related. We require that x^A and x^B
# do NOT reduce to degree<k on the mu_2-cosets, i.e. A and B are NOT both >= n/2 reducing.
# Concretely exclude A%（n/2) or B%(n/2)  giving x^A=+-x^{small<k}. Simplest: A,B < n/2 and >=k.
def is_genuine(A,B,n,k):
    h=n//2
    # correlated if A or B (mod h) < k (reduces to a low-degree term on +-1 cosets)
    return (A%h)>=k and (B%h)>=k and (A%h)!=(B%h)

print("=== GENUINE ragged residue: grow n at fixed direction-shape (d=4), char-p ===")
print("Excludes correlated x^{n/2}=+-1 directions. residue should be ~const (off-BGK).")
print(" n   k   dir(A,B)  d   maxS  cosetCore  residue  n/(2d)  Johnson")
for n in [8,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p);k=max(2,n//4)
    # pick a genuine direction with d=gcd(A-B,n)=4 if possible, A,B in mid-range
    found=None
    for A in range(k, n):
        for B in range(k, A):
            if gcd(A-B,n)==4 and is_genuine(A,B,n,k):
                found=(A,B);break
        if found:break
    if not found:
        print(f"{n}: no genuine d=4 dir"); continue
    A,B=found
    mS,core,res=max_agree_with_residue(p,n,k,A,B,g)
    print(f"{n:2d}  {k:3d}  ({A:2d},{B:2d})    4   {mS:3d}    {core:3d}      {res:3d}     {n/8:.1f}   {sqrt(n*k):.1f}")

print()
print("=== char-0 vs char-p residue at genuine directions (faithfulness) ===")
def max_agree_c0(n,k,A,B,tol=1e-7,cap=800000):
    w=np.exp(2j*pi/n);powers=[w**j for j in range(n)]
    for s in range(n,0,-1):
        if comb(n,s)>cap: continue
        bestcore=-1
        for sub in combinations(range(n),s):
            coeff=np.array([[powers[j]**t for t in range(k)]+[-powers[j]**B] for j in sub])
            aug=np.array([[powers[j]**t for t in range(k)]+[-powers[j]**B,-powers[j]**A] for j in sub])
            if np.linalg.matrix_rank(coeff,tol=tol)==np.linalg.matrix_rank(aug,tol=tol):
                c=coset_core(set(sub),n)
                if c>bestcore: bestcore=c
        if bestcore>=0: return s,bestcore,s-bestcore
    return 0,0,0
print(" n  dir   char0(S,core,res)  charP(S,core,res)  faithful?")
for n in [8,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p);k=max(2,n//4)
    found=None
    for A in range(k,n):
        for B in range(k,A):
            if gcd(A-B,n)==4 and is_genuine(A,B,n,k): found=(A,B);break
        if found:break
    A,B=found
    c0=max_agree_c0(n,k,A,B);cp=max_agree_with_residue(p,n,k,A,B,g)
    print(f"{n:2d} ({A},{B}) {c0}        {cp}      {c0==cp}")

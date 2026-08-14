import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# FINAL DECISIVE TEST: the TRUE max-agreement of a genuine monomial LINE x^a+gamma x^b
# (two-term, the actual prize object) with a single deg-<k codeword, exhaustively over
# ALL (a,b) directions with d=gcd(a-b,n)>=2 (genuine), and the ragged residue after
# stripping the maximal coset core. Test:
#  (1) is max-agreement <= Johnson sqrt(nk) for ALL genuine directions? (the R-thin BOUND)
#  (2) is char-p faithful to char-0 (no char-p excess at good radii)?
#  (3) reproduce comment-142's "ragged ~ 2k" and reconcile with realizability-excess.

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

def max_agree_line(p,n,k,A,B,g):
    """exhaustive max |S| realizable for two-term line x^A+gamma x^B vs deg-<k codeword.
    Returns (maxS, coreOfMaxS, residue)."""
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    def ok(sub):
        coeff=[];aug=[]
        for j in sub:
            xj=powers[j];row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,B,p))%p]
            coeff.append(row[:]);aug.append(row+[(-pow(xj,A,p))%p])
        return rank_modp(coeff,p)==rank_modp(aug,p)
    for s in range(n,0,-1):
        if comb(n,s)>1_200_000: continue
        bestcore=-1;bestsub=None
        for sub in combinations(range(n),s):
            if ok(sub):
                c=coset_core(set(sub),n)
                if c>bestcore: bestcore=c;bestsub=set(sub)
        if bestsub is not None:
            return s,bestcore,s-bestcore
    return 0,0,0

print("=== ALL genuine directions, max-agreement vs Johnson, n<=16 exhaustive ===")
print("Reports MAX over genuine dirs (d>=2): maxS, its coset core, ragged residue.")
print(" n  k  Johnson  MAXover-dirs(maxS)  worst-residue  worst-dir")
for n in [8,12,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p);k=max(2,n//4)
    overall_maxS=0; worst_res=0; worst_dir=None; res_maxS=0
    for A in range(1,n):
        for B in range(1,A):
            d=gcd(A-B,n)
            if d<2: continue
            mS,core,res=max_agree_line(p,n,k,A,B,g)
            if mS>overall_maxS: overall_maxS=mS
            if res>worst_res: worst_res=res; worst_dir=(A,B); res_maxS=mS
    print(f"{n:2d} {k:2d}  {sqrt(n*k):.1f}      {overall_maxS:3d}             {worst_res:3d}        {worst_dir}")

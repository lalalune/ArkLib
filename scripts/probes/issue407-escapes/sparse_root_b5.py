import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# SETTLE THE CENTRAL TENSION (comment 142 vs 125 vs 100):
# Quantity A (comment-142, the "Johnson-coincident" one): max RAGGED |S| over all directions
#   = total ragged agreement size including the imprimitive coset core.
# Quantity B (the REALIZABILITY EXCESS): max over directions of (|S| - generic_bound),
#   = how much the single-deg-<k constraint allows BEYOND the trivial k+1.
# The PRIZE needs the bad-SCALAR count, which via MonomialLineListBridge = list size of RS[k+1].
#
# The agreement set of x^a+gamma x^b with ONE deg-<k codeword. For the MONOMIAL direction
# x^k (the bridge object, comment 125 binding direction), bad scalars = leading coeffs of
# RS[k+1] codewords agreeing with u_0=x^k... but u_0 IS x^k itself here. Let's directly compute
# the bridge object: list size of RS[k+1] around a far word, at the crossing radius.
#
# Cleanest: compute exact max-agreement |S| of x^b with a single deg-<k poly (one-term line,
# the FarThresholdMaximality object), exhaustively, char-0 and char-p, and the BGK M(n) sum.

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
        M[r],M[piv]=M[piv],M[r];inv=pow(M[r][col],p-2,p)
        M[r]=[(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][col]%p!=0:
                f=M[i][col];M[i]=[(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows:break
    return r
def is_coset_union(s,n):
    for d in range(2,n+1):
        if n%d==0:
            sh=n//d
            if all(((j+sh)%n) in s for j in s):return False
    return True

# Exact max agreement of the TWO-TERM line x^A + gamma x^B with deg-<k codeword, char-p.
# S realizable iff augmented rank = coeff rank (over unknowns gamma, c_0..c_{k-1}).
def exact_max_realizable(p,n,k,A,B,g):
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    best_any=0;best_rag=0;cnt_rag=0
    # search descending size; for n<=16 exhaustive feasible
    for s in range(n,k,-1):
        if comb(n,s)>900000: continue
        got=False;ragsz=0;c=0
        for sub in combinations(range(n),s):
            coeff=[];aug=[]
            for j in sub:
                xj=powers[j]
                row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,B,p))%p]
                coeff.append(row[:]);aug.append(row+[(-pow(xj,A,p))%p])
            if rank_modp(coeff,p)==rank_modp(aug,p):
                got=True
                if is_coset_union(set(sub),n):
                    if s>ragsz: ragsz=s
                    c+=1
        if got and best_any==0: best_any=s
        if ragsz>0 and best_rag==0:
            best_rag=ragsz; cnt_rag=c
        if best_any>0 and best_rag>0: break
    return best_any,best_rag,cnt_rag

def bgk_M(p,n,g):
    e_exp=(p-1)//n;base=pow(g,e_exp,p);mu=[pow(base,j,p) for j in range(n)]
    w=np.exp(2j*pi/p);best=0.0
    for c in range(1,min(p,3000)):
        s=sum(w**((c*x)%p) for x in mu);best=max(best,abs(s))
    return best

print("=== EXACT (exhaustive) max-ragged + BGK side-by-side, char-p ===")
print("Binding low-exponent direction A=k+s (genuine imprimitive), B=k")
print(" n  k  prime  BGK_M  sqrt(n)  maxAny maxRag  k+1  Johnson  excess=Rag-(k+1)")
for n in [8,12,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p)
    k=max(2,n//4)
    M=bgk_M(p,n,g)
    # genuine imprimitive worst: pick d=2 (largest s=n/2)
    d=2; s=n//d; A=(k+s)%n; B=k
    if A==B: A=(A+1)%n
    ba,br,cr=exact_max_realizable(p,n,k,A,B,g)
    print(f"{n:2d} {k:2d} {p:5d} {M:5.2f}  {sqrt(n):5.2f}  {ba:3d}   {br:3d}    {k+1}   {sqrt(n*k):.2f}     {br-(k+1)}")

print()
print("=== char-0 vs char-p ragged at SAME direction (faithfulness test) ===")
def exact_max_realizable_c0(n,k,A,B,tol=1e-7):
    w=np.exp(2j*pi/n);powers=[w**j for j in range(n)]
    best_any=0;best_rag=0;cnt=0
    for s in range(n,k,-1):
        if comb(n,s)>500000: continue
        got=False;ragsz=0;c=0
        for sub in combinations(range(n),s):
            # rank over C: build coeff matrix and augmented, compare numerical ranks
            coeff=np.array([[powers[j]**t for t in range(k)]+[-powers[j]**B] for j in sub])
            aug=np.array([[powers[j]**t for t in range(k)]+[-powers[j]**B, -powers[j]**A] for j in sub])
            rc=np.linalg.matrix_rank(coeff,tol=tol); ra=np.linalg.matrix_rank(aug,tol=tol)
            if rc==ra:
                got=True
                if is_coset_union(set(sub),n):
                    if s>ragsz: ragsz=s
                    c+=1
        if got and best_any==0:best_any=s
        if ragsz>0 and best_rag==0: best_rag=ragsz;cnt=c
        if best_any>0 and best_rag>0: break
    return best_any,best_rag,cnt
print(" n  k  (A,B)  char0(any,rag)  charP(any,rag)")
for n in [8,12,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p);k=max(2,n//4)
    d=2;s=n//d;A=(k+s)%n;B=k
    if A==B:A=(A+1)%n
    c0=exact_max_realizable_c0(n,k,A,B)
    cp=exact_max_realizable(p,n,k,A,B,g)
    print(f"{n:2d} {k:2d} ({A},{B}) ({c0[0]},{c0[1]})        ({cp[0]},{cp[1]})")

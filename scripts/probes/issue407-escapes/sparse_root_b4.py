import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# SCALING TEST + BGK SIDE-BY-SIDE.
# For the genuine imprimitive direction (a,b)=(2d, d) gives a-b=d so x^a+gamma x^b
# = x^d(x^d + gamma)  -- factors!  The agreement set lives on cosets of mu_{n/gcd}.
# More honest genuine direction per Kambire: a-b = d with d | n, d>=2, worst d ~ n/44.
#
# We can't enumerate large n. Instead use the STRUCTURAL realizability fact:
# the max agreement of x^a + gamma x^b with deg-<k poly. On mu_n with x^n=1, x^a=x^{a%n} etc.
# The agreement poly Q = x^{a%n} + gamma x^{b%n} - c(x), deg < n. Its mu_n roots = S.
# This is a (k+2)-sparse poly (support {a%n, b%n} U {0..k-1}).
# By Descartes-for-roots-of-unity (Bombieri-Zannier / the "fewnomials over mu_n" bound):
# # roots in mu_n of a t-term integer/cyclotomic poly with no cyclotomic-coset factor
# is bounded INDEPENDENT of degree.
#
# We test the SCALING of the EXACT max-ragged via a targeted search:
# realizability = consistency of the (k+1)-unknown linear system. The MAX consistent S
# has |S| determined by rank. We compute the max over a smart sample of directions.

def primitive_root_mod_p(p):
    if p == 2: return 1
    phi = p-1; mm = phi; d = 2; fac=[]
    while d*d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm//=d
        d+=1
    if mm>1: fac.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None
def find_thin_prime(n, lo):
    t=(lo-1)//n+1
    while True:
        p=1+n*t
        if isprime(p): return p
        t+=1

# BGK quantity: M(n) = max_{c!=0} |sum_{x in mu_n} e_p(c x)|  (the per-frequency char sum)
def bgk_M(p,n,g):
    e_exp=(p-1)//n; base=pow(g,e_exp,p)
    mu=[pow(base,j,p) for j in range(n)]
    w=np.exp(2j*pi/p)
    best=0.0
    # sample c over a coset rep set + random
    import random
    cs = list(range(1,min(p,2000)))
    for c in cs:
        s=sum(w**((c*x)%p) for x in mu)
        best=max(best, abs(s))
    return best

# The ragged max via realizability: for a fixed direction, the max agreement set size is
# the largest s such that some s-subset S of mu_n has the augmented linear system consistent.
# Equivalent: the agreement poly x^A + gamma x^B - c has s roots in mu_n with the SAME (gamma,c).
# The number of (gamma,c) DOF is k+1. A set of s>k+1 points imposes s-(k+1) extra linear
# constraints that must be auto-satisfied = a RANK DEFICIENCY of the (s)x(k+1) matrix being
# < s but consistent. We compute the GENERIC max: it's k+1 unless special alignment.
# The realizability EXCESS over k+1 is exactly what we measure.

def rank_modp(M,p):
    M=[[x%p for x in row] for row in M]; rows=len(M); cols=len(M[0]) if rows else 0; r=0
    for col in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i][col]%p!=0: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; inv=pow(M[r][col],p-2,p)
        M[r]=[(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][col]%p!=0:
                f=M[i][col]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows:break
    return r
def is_coset_union(ssub,n):
    for d in range(2,n+1):
        if n%d==0:
            sh=n//d
            if all(((j+sh)%n) in ssub for j in ssub): return False
    return True

def max_agreement_smart(p,n,k,A,B,g,trials=40000):
    """Monte-Carlo + greedy: find large realizable agreement sets. Returns (best_any,best_ragged)."""
    import random
    e_exp=(p-1)//n; base=pow(g,e_exp,p)
    powers=[pow(base,j,p) for j in range(n)]
    def realizable(sub):
        coeff=[];aug=[]
        for j in sub:
            xj=powers[j]
            row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,B,p))%p]
            coeff.append(row[:]); aug.append(row+[(-pow(xj,A,p))%p])
        return rank_modp(coeff,p)==rank_modp(aug,p)
    best_any=0;best_rag=0
    # greedy growth from random seeds
    idx=list(range(n))
    for _ in range(trials):
        random.shuffle(idx)
        S=[]
        for j in idx:
            if realizable(S+[j]):
                S.append(j)
        if len(S)>best_any: best_any=len(S)
        if is_coset_union(set(S),n) and len(S)>best_rag: best_rag=len(S)
        if best_any>=k+1+ n//4: pass
    return best_any,best_rag

print("=== SCALING: max-ragged at FIXED RATE rho=1/4, genuine imprimitive direction ===")
print("Direction A=k+s, B=k where s=n/d (Kambire worst ~ n/44, here we sweep d)")
print(" n   k   d   s=n/d  maxAny  maxRagged  k+1  Johnson  ragged-(k+1)")
for n in [8,16,32,64]:
    p=find_thin_prime(n,2000); g=primitive_root_mod_p(p)
    k=max(2,n//4)
    for d in [2,4,n//4]:
        if d<2 or n%d: continue
        s=n//d
        A=(k+d)%n; B=k%n
        if A==B: A=(k+d+1)%n
        tr = 6000 if n<=32 else 2500
        ba,br=max_agreement_smart(p,n,k,A,B,g,trials=tr)
        print(f"{n:3d} {k:3d} {d:3d}  {s:4d}    {ba:3d}     {br:3d}     {k+1}   {sqrt(n*k):.2f}    {br-(k+1)}")

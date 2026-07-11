import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# THE KAMBIRE WORST DIRECTION: large d, small s=n/d. comment 133 says the gap is a CONSTANT
# approx s/4 ~ 10 there, independent of n. We test:
#  - the max-agreement |S| of x^A + gamma x^B at direction with d=gcd(A-B,n) large.
#  - SEPARATE the coset core (size n/(2d) per the autocorrelation bound) from the genuine
#    ragged residue (granularity-1, the _RaggedRootBound reduced set).
#  - Is the residue O(s) = O(constant) at fixed s, INDEPENDENT of n? (off-BGK)
#    or does it grow with n at fixed s? (= BGK)
#
# Decisive: FIX s (so the direction is "the same shape") and GROW n. If residue grows -> BGK.

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

def largest_coset_core(s_set, n):
    """Return size of largest mu_d-coset-union contained in s_set (the coset core)."""
    best=0
    for d in range(2,n+1):
        if n%d: continue
        sh=n//d  # shift in exponent for a mu_d coset (orbit under +sh, size d)
        # orbits of +sh on Z/n: there are sh=n/d orbits each of size d
        seen=set();core=0
        for start in range(sh):
            orbit=[(start + j*sh)%n for j in range(d)]
            if all(o in s_set for o in orbit):
                core += d
        best=max(best,core)
    return best

# greedy-max realizable agreement set (Monte-Carlo for larger n)
def max_realizable_mc(p,n,k,A,B,g,trials):
    import random
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    def ok(sub):
        coeff=[];aug=[]
        for j in sub:
            xj=powers[j];row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,B,p))%p]
            coeff.append(row[:]);aug.append(row+[(-pow(xj,A,p))%p])
        return rank_modp(coeff,p)==rank_modp(aug,p)
    bestS=[]; idx=list(range(n))
    for _ in range(trials):
        random.shuffle(idx);S=[]
        for j in idx:
            if ok(S+[j]): S.append(j)
        if len(S)>len(bestS): bestS=S[:]
    return bestS

print("=== FIX s, GROW n: does ragged RESIDUE (|S|-core) grow with n? (BGK test) ===")
print("Direction A=B+s with s fixed, B=k, d=gcd(s,n). Genuine when d=gcd>=2.")
print("Key: residue = |S| - largest_coset_core. If residue ~ const(s) indep of n -> OFF BGK.")
print()
print(" s   n    k   |S|max  cosetCore  residue  s/4  Johnson")
for s in [4, 8]:
    for n in [32, 64, 128]:
        if n % s: continue
        k=max(2,n//4)
        B=k; A=(B+s)%n
        d=gcd(s,n)
        if d<2: continue
        p=find_thin_prime(n,5000);g=primitive_root_mod_p(p)
        tr = 2000 if n<=64 else (500 if n<=128 else 150)
        S=max_realizable_mc(p,n,k,A,B,g,tr)
        core=largest_coset_core(set(S),n)
        print(f"{s:2d}  {n:4d}  {k:3d}   {len(S):4d}   {core:4d}      {len(S)-core:4d}   {s/4:.1f}  {sqrt(n*k):.1f}")
    print()

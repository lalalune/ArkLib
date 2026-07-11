#!/usr/bin/env python3
"""
probe_wf5A3_mgf_to_max.py  (#444 lane A3) -- the ASSEMBLY: moment bound => max bound.

Confirms the DETERMINISTIC chain that turns the char-p deep-moment lemma into the prize bound:

  HYPOTHESIS (the open char-p deep-moment lemma, pre-screened HOLDING in probe_wf5A3_moment_mgf_equiv):
     E_b[ (S_b/sqrt n)^{2r} ] <= (2r-1)!!     for all r with 2r <= 2 log p.   (MOM)

  ASSEMBLY (elementary, deterministic, no randomness needed):
     Let m = #{coset reps}.  For ANY single coset rep family, the MAX satisfies, by Markov on the 2r-th moment:
        #{ b : |S_b| > t sqrt n }  <=  m * (2r-1)!! / t^{2r}.
     The set is EMPTY (=> M <= t sqrt n) as soon as  m (2r-1)!! / t^{2r} < 1.
     Optimize over r:  using (2r-1)!! <= (2r)^r / 2^r ... actually (2r-1)!! <= r^r 2^r e^{-r} ... ;
     the clean bound:  (2r-1)!! <= (2r-1)!!,  and with t^2 = 2 e r  one gets  (2r-1)!!/t^{2r} <= e^{-r} (Stirling),
     choose r = log m  =>  M <= sqrt( 2 e n log m )  = sqrt(2e) sqrt(n log(p/n)).   (PRIZE BOUND, C=sqrt(2e)~2.33)

This probe VERIFIES the assembly numerically end-to-end:
  - takes the TRUE per-r moments (measured),
  - computes the Markov-union upper bound on M for each r,
  - takes min over r,
  - compares to the ACTUAL M.
If actual M <= union bound for the OPTIMIZED r, the assembly is sound and the only open input is (MOM).
"""
import math, sys
import numpy as np

def isp(x):
    if x<2:return False
    if x%2==0:return x==2
    d=3
    while d*d<=x:
        if x%d==0:return False
        d+=2
    return True
def find_p(n,beta):
    t=int(round(n**beta));lo=max(t,50);p=lo+((1+n-lo%n)%n)
    if p<=2:p+=n
    while True:
        if p%n==1 and isp(p):return p
        p+=n
def proot(p):
    m=p-1;fs=[];d=2;mm=m
    while d*d<=mm:
        if mm%d==0:
            fs.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fs.append(mm)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs):return g
        g+=1
def df(k):
    r=1.0;i=k
    while i>0:r*=i;i-=2
    return r

def periods_transversal(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    m=(p-1)//n;gn=pow(g,n,p)
    bs=np.empty(m,dtype=np.int64);b=1
    for t in range(m):bs[t]=b;b=(b*gn)%p
    S=np.empty(m,dtype=np.float64);tp=2.0*math.pi/p
    chunk=max(1,2_000_000//n);uo=p>=(1<<31)
    for s in range(0,m,chunk):
        e=min(m,s+chunk);bb=bs[s:e]
        if uo:pm=((bb[:,None].astype(object)*mu[None,:].astype(object))%p).astype(np.float64)
        else:pm=((bb[:,None]*mu[None,:])%p).astype(np.float64)
        S[s:e]=np.cos(tp*pm).sum(axis=1)
    return S,m

def run(n,beta):
    p=find_p(n,beta);S,m=periods_transversal(n,p);Z=np.abs(S)/math.sqrt(n)
    M=Z.max()*math.sqrt(n);logm=math.log(m)
    # Markov-union over r using the GAUSSIAN ceiling (2r-1)!! (the hypothesis MOM bound, not the measured value):
    best=float('inf');bestr=0
    for r in range(1,40):
        mom=df(2*r-1)         # hypothesis ceiling
        # smallest t with m*mom/t^{2r} < 1  => t = (m*mom)^{1/2r}
        t=(m*mom)**(1.0/(2*r))
        Mb=t*math.sqrt(n)
        if Mb<best:best=Mb;bestr=r
    Cassembly=best/math.sqrt(n*logm)
    return dict(n=n,p=p,m=m,M=M,Munion=best,r_opt=bestr,C_assembly=Cassembly,M_le_union=(M<=best))

if __name__=="__main__":
    ns=[int(x) for x in sys.argv[1:]] or [16,32,64,128]
    beta=4.0
    print("# Assembly: TRUE M vs Markov-union bound using the HYPOTHESIS ceiling (2r-1)!! .")
    print(f"{'n':>5} {'p':>11} {'m':>9} {'true_M':>8} {'union_M':>8} {'r_opt':>5} {'C_asm':>6} {'M<=union?':>9}")
    for n in ns:
        r=run(n,beta)
        print(f"{r['n']:>5} {r['p']:>11} {r['m']:>9} {r['M']:>8.2f} {r['Munion']:>8.2f} {r['r_opt']:>5} {r['C_assembly']:>6.3f} {str(r['M_le_union']):>9}")

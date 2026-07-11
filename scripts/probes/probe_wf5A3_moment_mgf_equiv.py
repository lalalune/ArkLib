#!/usr/bin/env python3
"""
probe_wf5A3_moment_mgf_equiv.py  (#444 lane A3)

VERIFY the A3 reduction's engine:  the deterministic Salem-Zygmund MGF bound (SG)
   E_b[ exp(lambda S_b/sqrt n) ] <= exp(C lambda^2/2)
is, term by term, the CHAR-p DEEP-MOMENT statement (the meta-theorem's unique permitted route).

Identity (exact, no randomness):  averaging over the FULL group b in F_p^* (not just transversal),
   M_2r := (1/(p-1)) sum_{b!=0} S_b^{2r}
         = #{ (x_1..x_2r) in mu_n^{2r} : x_1+...+x_r = x_{r+1}+...+x_{2r}  (mod p) }  / 1 ...
   more precisely  sum_{b in F_p} S_b^{2r} = p * E_{2r},   E_{2r}= #{signed 2r-subset sums = 0 mod p with the +/- pattern}.
We use S_b real, S_b = sum_{x in mu_n} e_p(bx) restricted; the raw 2r-th moment of S_b over b
counts 2r-fold additive coincidences of mu_n mod p.  E[Z^{2r}] = M_2r / n^r.

CHAR-0 (Lam-Leung) bound:  the number of such coincidences that hold OVER Z is the Gaussian/Wick
count (2r-1)!! * n^r * (1+o(1)) for the antipodal 2-power group.  =>  E[Z^{2r}] -> (2r-1)!! = Gaussian.
The OPEN part: SPURIOUS mod-p coincidences (vanish mod p, not over Z) at depth r ~ log p.

This probe MEASURES the standardized moments  E[Z^{2r}]  for r=1..R over the full b-family and compares
to the Gaussian value (2r-1)!!.  If E[Z^{2r}] <= (2r-1)!! * (1+small) up to r~log p, the MGF (SG) holds
=> prize bound.  We report the moment RATIO  E[Z^{2r}] / (2r-1)!!  vs r and vs n  (must stay O(1)).
"""
import math, sys
import numpy as np

def isp(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True

def find_p(n,beta):
    target=int(round(n**beta)); lo=max(target,50)
    p=lo+((1+n-lo%n)%n)
    if p<=2: p+=n
    while True:
        if p%n==1 and isp(p): return p
        p+=n

def proot(p):
    m=p-1; fs=[]; d=2; mm=m
    while d*d<=mm:
        if mm%d==0:
            fs.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fs.append(mm)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs): return g
        g+=1

def double_fact(k):  # (2r-1)!! for k=2r-1
    r=1.0; i=k
    while i>0:
        r*=i; i-=2
    return r

def all_periods_full(n,p):
    """S_b for ALL b in 1..p-1 (full group)."""
    g=proot(p); h=pow(g,(p-1)//n,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    bs=np.arange(1,p,dtype=np.int64)
    twopi=2.0*math.pi/p
    S=np.empty(p-1,dtype=np.float64)
    chunk=max(1, 4_000_000//n)
    use_obj = p>=(1<<31)
    for s in range(0,p-1,chunk):
        e=min(p-1,s+chunk)
        bb=bs[s:e]
        if use_obj:
            pm=((bb[:,None].astype(object)*mu[None,:].astype(object))%p).astype(np.float64)
        else:
            pm=((bb[:,None]*mu[None,:])%p).astype(np.float64)
        S[s:e]=np.cos(twopi*pm).sum(axis=1)
    return S

def run(n,beta,R):
    p=find_p(n,beta)
    S=all_periods_full(n,p)
    Z=S/math.sqrt(n)
    out=[]
    for r in range(1,R+1):
        m2r=np.mean(Z**(2*r))
        gauss=double_fact(2*r-1)
        out.append((r,m2r,gauss,m2r/gauss))
    logp=math.log(p)
    return p,logp,out

if __name__=="__main__":
    ns=[int(x) for x in sys.argv[1:]] or [16,32,64,128]
    beta=4.0; R=8
    print(f"# E[Z^2r]/(2r-1)!!  (Gaussian=1).  Must stay O(1) up to r~log p ~ {beta}*log n for the prize.")
    for n in ns:
        p,logp,out=run(n,beta,R)
        print(f"\n n={n} p={p} log p={logp:.2f}  (depth needed r~{logp:.0f})")
        for r,m2r,g,ratio in out:
            flag = " <== beyond proven r=3" if r>3 else ""
            print(f"   r={r:2d}  E[Z^{2*r:2d}]={m2r:12.3f}  (2r-1)!!={g:12.1f}  ratio={ratio:7.4f}{flag}")

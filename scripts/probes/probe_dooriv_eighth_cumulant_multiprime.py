#!/usr/bin/env python3
"""
probe_dooriv_eighth_cumulant_multiprime.py (#444, door-(iv) marginal moment ladder) -- DECISIVE.
8th normalized connected cumulant g4 at 3 structured primes per n. VERDICT: g4 across-prime sd
DOMINATES the mean and SIGN FLIPS prime-to-prime (n=32:+0.26,-0.36,-0.36; n=64:+0.42,-0.06,+1.54;
n=128:-0.59,+0.34,-0.23), mean consistent with 0 => finite-size SAMPLING NOISE, NO stable
non-Gaussian 8th-order signal. The apparent single-prime 8th-order 'growth' was a sampling artifact.
HONEST: data too noisy for an axiom-clean 8th-order vanishing; the conclusion is 'no signal'. The
marginal moment ladder stays Gaussian-collapsed (capstone _DoorIVMomentLadderWickCollapse.lean).
"""
import numpy as np
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
def prr(p):
    phi=p-1;fac=set();t=phi;d=2
    while d*d<=t:
        while t%d==0: fac.add(d);t//=d
        d+=1
    if t>1: fac.add(t)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g
def primes(n,beta,c):
    out=[];lo=max(round(n**beta),n**3+1);p=lo-(lo%n)+1
    if p<=lo:p+=n
    while len(out)<c:
        if isprime(p): out.append(p)
        p+=n
    return out
def g4(x):
    x=np.asarray(x,float);xc=x-x.mean()
    m2=(xc**2).mean();m4=(xc**4).mean();m6=(xc**6).mean();m8=(xc**8).mean()
    return (m8-28*m6*m2-35*m4**2+420*m4*m2**2-630*m2**4)/m2**4
def per(n,p,mr=80000,seed=11):
    g=prr(p);m=(p-1)//n
    H=np.array([pow(g,(m*j)%(p-1),p) for j in range(n)],dtype=object)
    tp=2*np.pi/p
    ts=list(range(m)) if m<=mr else np.random.default_rng(seed).choice(m,mr,replace=False)
    et=np.empty(len(ts))
    for i,t in enumerate(ts):
        b=pow(g,int(t),p);res=((int(b)*H)%p).astype(np.float64);et[i]=np.cos(tp*res).sum()
    return et
print("n   per-prime g4 ...           mean+/-sd")
for n in (32,64,128):
    ps=primes(n,4.0,3);gs=[g4(per(n,p,seed=10+i)) for i,p in enumerate(ps)]
    print(f"{n:>4} "+"  ".join(f"{v:+.3f}" for v in gs)+f"   {np.mean(gs):+.3f}+/-{np.std(gs):.3f}")

import numpy as np
from math import gcd, log, sqrt

def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def fact2(k):
    r=1
    for j in range(1,2*k,2): r*=j
    return r

def subgroup(p,n):
    e=(p-1)//n
    for cand in range(2,p):
        h=pow(cand,e,p)
        if h==1 or pow(h,n//2,p)==1: continue
        S=set(); x=1
        for _ in range(n): x=(x*h)%p; S.add(x)
        if len(S)==n: return np.array(sorted(S))
    raise RuntimeError

def oddpart(m):
    while m%2==0: m//=2
    return m

def analyze(p,n,rmax=10):
    S=subgroup(p,n); b=np.arange(p)
    eta=np.zeros(p,dtype=complex); ang=2j*np.pi/p
    for x in S: eta+=np.exp(ang*((b*x)%p))
    mag2=np.abs(eta[1:])**2          # b!=0
    M=sqrt(mag2.max())
    # best moment bound: min_r (sum_{b!=0}|eta|^{2r})^{1/2r}
    best=1e18; bestr=0; cum_ratio={}
    for r in range(1,rmax+1):
        Sr=(mag2**r).sum()
        bound=Sr**(1.0/(2*r))
        cum_ratio[r]=(Sr/p)/(fact2(r)*n**r)
        if bound<best: best=bound; bestr=r
    return M, best, bestr, cum_ratio

def findp(n,tgt):
    for m in range(tgt,tgt*8):
        p=n*m+1
        if isprime(p): return p,m
    return None,None

print("=== M(n,p), best moment bound, vs target sqrt(2 n ln p); cumulant ratios r=1..10 ===")
print("oddpart(p-1) small => 2-power-structured (heavy).  cum ratio>1 => super-Wick\n")
for n in [16,32,64]:
    print(f"--- n={n} ---")
    for tgt in [16,64,256,1024,4096]:
        p,m=findp(n,tgt)
        if p is None or p>2_000_000: continue
        M,best,br,cr=analyze(p,n)
        tgt_bound=sqrt(2*n*log(p))
        op=oddpart(p-1)
        cs=" ".join(f"{cr[r]:.2f}" for r in range(1,11))
        flag="HEAVY" if any(cr[r]>1.2 for r in cr) else "    "
        print(f" p={p:8d} idx={m:5d} oddpart(p-1)={op:7d} | M/√n={M/sqrt(n):.2f} best/√n={best/sqrt(n):.2f}(r={br}) tgt/√n={tgt_bound/sqrt(n):.2f} {flag}")
        print(f"     cum r1..10: {cs}")
    print()

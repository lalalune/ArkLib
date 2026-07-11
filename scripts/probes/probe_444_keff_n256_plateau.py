#!/usr/bin/env python3
# 4th point n=256 (plateau-vs-diverge): does the peak-K_eff creep continue above n=128's [0.653,0.698]?
# Trick: pick p JUST UNDER 2^32 (beta=log_256 p ~ 3.9999 ~ 4) so t*x < 2^64 fits uint64 -> numpy modmul
# with NO overflow (full-spectrum dense method, exact S1 convention).
import math, numpy as np
def isp(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True
def proot(p):
    m=p-1; fs=[]; d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.append(m)
    g=2
    while not all(pow(g,(p-1)//f,p)!=1 for f in fs): g+=1
    return g
def v2(x):
    v=0
    while x%2==0: x//=2; v+=1
    return v
def good_primes_below(n, count, cap):
    # primes p == 1 mod n, p < cap, v2(p-1)=log2(n) (m odd = "good"), largest first
    mu2=int(round(math.log2(n)))
    out=[]; p=cap - (cap%n) + 1
    if p>=cap: p-=n
    while len(out)<count and p>n:
        if p%n==1 and isp(p) and v2(p-1)==mu2:
            out.append(p)
        p-=n
    return out
def dfact(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v
def peakK(n,p):
    g=proot(p); h=pow(g,(p-1)//n,p); m=(p-1)//n; gn=pow(g,n,p)
    mu=[pow(h,j,p) for j in range(n)]
    # build transversal b=(g^n)^k via fast python list (numpy scalar setitem is slow)
    lst=[0]*m; b=1
    for k in range(m): lst[k]=b; b=b*gn%p
    bl=np.array(lst,dtype=np.uint64); del lst
    print(f"    [p={p}: transversal built]", flush=True)
    acc=np.zeros(m,dtype=np.float64); c=2.0*np.pi/p; P=np.uint64(p)
    for x in mu:
        t=(bl*np.uint64(x))%P          # uint64, no overflow since p<2^32
        acc+=np.cos(c*t.astype(np.float64))
    e2=acc*acc
    rmax=int(1.4*math.log(p)); mx=0.0; ar=0
    for r in range(1,rmax+1):
        k=(np.sum(e2**r)/p/(dfact(r)*(n**r)))**(1.0/r)
        if k>mx: mx=k; ar=r
    return mx,ar,rmax,m
def main():
    n=256; cap=2**32
    ps=good_primes_below(n,4,cap)[2:]   # primes 3 and 4 (1,2 already measured: 0.653, 0.703)
    print(f"# n={n} plateau-vs-diverge; primes 3-4 just under 2^32 (beta~4.000)", flush=True)
    peaks=[]
    for p in ps:
        mx,ar,rmax,m=peakK(n,p)
        beta=math.log(p)/math.log(n)
        print(f"  p={p} beta={beta:.4f} v2={v2(p-1)} m={m} rmax={rmax}  peak K_eff={mx:.3f}@r{ar}", flush=True)
        peaks.append(mx)
    lo,hi=min(peaks),max(peaks); mean=sum(peaks)/len(peaks)
    print(f"  n=256 peak K_eff mean={mean:.3f} range[{lo:.3f},{hi:.3f}]")
    print()
    print("Series (good primes): n=32:[.577,.629] n=64:[.614,.645] n=128:[.653,.698] n=256:[above]")
    print("=> band ABOVE .698 (continues separating): creep CONTINUES (diverge-leaning, BGK log-growth).")
    print("=> band overlapping/below .698: PLATEAU (energy-route bounded-K hope survives).")
if __name__=='__main__':
    main()

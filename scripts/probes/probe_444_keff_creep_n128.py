#!/usr/bin/env python3
# Is the peak-K_eff "flat in n" (S1) or slowly creeping (BGK wall)? Single points were noisy
# (n=32:0.612, n=64:0.597, n=128:0.653). Sample SEVERAL good primes per n to get the variation band,
# so noise vs n-creep can be separated.  Exact S1 convention.
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
def good_primes(n, count, lo):
    # primes p == 1 mod n, near beta=4, with v2(p-1)=log2(n) (m odd) = "good"
    mu2=int(round(math.log2(n)))
    out=[]; p=lo+((1+n-lo%n)%n)
    if p<=2: p+=n
    while len(out)<count:
        if p>2 and p%n==1 and isp(p) and v2(p-1)==mu2:
            out.append(p)
        p+=n
    return out
def dfact(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v
def peakK(n,p):
    g=proot(p); h=pow(g,(p-1)//n,p); m=(p-1)//n; gn=pow(g,n,p)
    mu=[pow(h,j,p) for j in range(n)]
    b=1; bl=[0]*m
    for k in range(m): bl[k]=b; b=b*gn%p
    barr=np.array(bl,dtype=np.int64)
    acc=np.zeros(m,dtype=np.float64); c=2*np.pi/p
    for x in mu: acc+=np.cos(c*((barr*int(x))%p))
    e2=acc*acc
    rmax=int(1.4*math.log(p)); mx=0.0; ar=0
    for r in range(1,rmax+1):
        k=(np.sum(e2**r)/p/(dfact(r)*(n**r)))**(1.0/r)
        if k>mx: mx=k; ar=r
    return mx,ar,rmax
def main():
    print("# peak K_eff across several good primes per n (beta~4) -- noise band vs n-creep")
    for n in (32,64,128):
        ps=good_primes(n,4,n**4)
        res=[peakK(n,p) for p in ps]
        peaks=[r[0] for r in res]
        lo,hi=min(peaks),max(peaks); mean=sum(peaks)/len(peaks)
        detail=" ".join(f"{p}:{mx:.3f}@r{ar}" for p,(mx,ar,rm) in zip(ps,res))
        print(f"n={n:3d}: peak K_eff mean={mean:.3f} range[{lo:.3f},{hi:.3f}]  ({detail})")
    print()
    print("If the per-n ranges OVERLAP across n => flat-in-n consistent (noise).")
    print("If n=128 range sits ABOVE n=64/n=32 => genuine upward creep (BGK log-growth showing).")
if __name__=='__main__':
    main()

#!/usr/bin/env python3
# Prize-relevant gap I haven't measured: the K_eff peak across the PRIZE beta-band (beta=log_n p ~ 4-5).
# S1 + all my prior work fixed beta=4. ABF prize regime is beta in [4,5]. Does K_eff worsen at beta=5?
# (Higher beta = larger p = more frequencies + deeper rmax; the char-p wraparound contribution is
# beta-dependent.) Exact S1 convention; pick p<2^32 so t*x fits uint64.
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
def good_prime_near(n, target, cap=2**32):
    # smallest prime p>=target, p==1 mod n, v2(p-1)=log2 n (good/prize-rep), p<cap
    mu2=int(round(math.log2(n))); p=target+((1+n-target%n)%n)
    while p<cap:
        if p%n==1 and isp(p) and v2(p-1)==mu2: return p
        p+=n
    return None
def dfact(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v
def peakK(n,p):
    g=proot(p); h=pow(g,(p-1)//n,p); m=(p-1)//n; gn=pow(g,n,p)
    mu=[pow(h,j,p) for j in range(n)]
    b=1; lst=[0]*m
    for k in range(m): lst[k]=b; b=b*gn%p
    bl=np.array(lst,dtype=np.uint64); del lst
    acc=np.zeros(m,dtype=np.float64); c=2.0*np.pi/p; P=np.uint64(p)
    for x in mu: acc+=np.cos(c*((bl*np.uint64(x))%P).astype(np.float64))
    e2=acc*acc; rmax=int(1.4*math.log(p)); mx=0.0; ar=0
    for r in range(1,rmax+1):
        k=(np.sum(e2**r)/p/(dfact(r)*(n**r)))**(1.0/r)
        if k>mx: mx=k; ar=r
    return mx,ar,rmax
def main():
    print("# K_eff peak across the PRIZE beta-band (beta=log_n p); does it worsen toward beta=5?")
    for n in (32,64):
        row=[]
        for beta in (3.0,3.5,4.0,4.5,5.0):
            target=int(round(n**beta))
            if target>=2**32: row.append((beta,None)); continue
            p=good_prime_near(n,target)
            if p is None: row.append((beta,None)); continue
            mx,ar,rmax=peakK(n,p)
            beff=math.log(p)/math.log(n)
            row.append((beta,(p,beff,mx,ar)))
            print(f"  n={n:3d} beta~{beta:.1f} p={p:>11} (beff={beff:.2f}) peak K_eff={mx:.3f}@r{ar}", flush=True)
        ks=[r[1][2] for r in row if r[1]]
        if ks: print(f"  -> n={n}: K_eff peak across beta 3..5 = [{min(ks):.3f},{max(ks):.3f}], spread {max(ks)-min(ks):.3f}")
    print()
    print("READ: flat across beta=3..5 => prize beta-band not special, n-trend (plateau ~0.67) is the story.")
    print("      rising toward beta=5 => the UPPER prize end is worse; must target beta=5, not just 4.")
if __name__=='__main__':
    main()

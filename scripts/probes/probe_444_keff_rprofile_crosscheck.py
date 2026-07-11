#!/usr/bin/env python3
# TRUE cross-check of S1's K_eff (matching wfS1_energy_transfer_keff.rs EXACTLY):
#   b iterates over the order-m subgroup (g^n)^k, k=0..m-1  (m distinct mu_n-coset values of eta_b),
#   E_r' = (1/p) * sum_b eta_b^{2r},  K_eff(r) = (E_r' / [(2r-1)!! * n^r])^{1/r}.
# Adds the full r-PROFILE (S1 reported only MAX): does K_eff(r) grow or fall toward r~1.4 ln q?
import math
def isp(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def fp(n,lo):
    p=lo+((1+n-lo%n)%n)
    if p<=2: p+=n
    while not (p>2 and p%n==1 and isp(p)): p+=n
    return p
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
def lpf(x):
    L=1; d=2
    while d*d<=x:
        while x%d==0: L=d; x//=d
        d+=1
    if x>1: L=x
    return L
def dfact(r):
    v=1.0
    for j in range(1,r+1): v*=(2*j-1)
    return v
def run(n,p,tag):
    import numpy as np
    g=proot(p); h=pow(g,(p-1)//n,p); m=(p-1)//n; gn=pow(g,n,p)
    mu=[pow(h,j,p) for j in range(n)]
    # eta over b=(g^n)^k  (m coset values), exactly as the Rust does
    eta=np.empty(m,dtype=np.float64); b=1
    mu_arr=np.array(mu,dtype=np.float64)
    for k in range(m):
        t=(b*mu_arr)%p
        eta[k]=np.sum(np.cos(2*np.pi*t/p))
        b=(b*gn)%p
    lnq=math.log(p); rmax=int(1.4*lnq)
    e2=eta*eta
    prof=[]
    for r in range(1,rmax+1):
        er=np.sum(e2**r)/p
        ratio=er/(dfact(r)*(n**r))
        prof.append((r, ratio**(1.0/r)))
    mx=max(k for _,k in prof)
    amax=max(prof,key=lambda t:t[1])
    # r-trend from the argmax onward toward rmax
    deep=[k for r,k in prof if r>=max(2,rmax//2)]
    trend = "GROWS" if prof[-1][1] > amax[1]+0.01 else ("flat~" if abs(prof[-1][1]-prof[rmax//2-1][1])<0.03 else "falls")
    samp=" ".join(f"r{r}:{k:.3f}" for r,k in prof if r in (1,2,3,rmax//2,rmax-1,rmax))
    print(f"{tag:6} n={n:3d} p={p:>11} v2={v2(p-1):2d} lpf={lpf((p-1)//n):>9} lnq={lnq:.0f} beta={lnq/math.log(n):.2f} "
          f"MAXK={mx:.3f}@r{amax[0]} trend={trend}  [{samp}]")
    return mx, amax, prof
def main():
    print("# TRUE cross-check of S1 K_eff (exact Rust convention) + full r-profile")
    print("== n=32, beta~4 ==")
    run(32, fp(32,32**4), "good")
    p=fp(32,1000003)
    for _ in range(4000):
        q=fp(32,p+1)
        if v2(q-1)>=10: run(32,q,"hi-v2"); break
        p=q
    p=fp(32,1000003)
    for _ in range(6000):
        q=fp(32,p+1)
        if lpf((q-1)//32)>(q-1)//32//4: run(32,q,"rough"); break
        p=q
    print("== n=64, beta~4 ==")
    run(64, fp(64,64**4), "good")
    print()
    print("S1 reported MAX K_eff: 0.62 (n=32 good), 0.56 (hi-v2), 0.58 (rough), 0.65 (n=64 good).")
    print("KEY r-PROFILE: GROWS => r~89 (n=2^30) extrapolation unsafe (BGK wall); flat/falls => optimistic frontier supported.")
if __name__=='__main__':
    main()

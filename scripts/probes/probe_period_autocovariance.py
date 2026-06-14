import math, cmath, statistics
# CONFIRM the workflow's load-bearing reversal: are the Gauss periods log-correlated (FHK, -3/4 subleading)
# or near-INDEPENDENT white noise (iid-Gumbel, -1/2 subleading)? Measure the autocovariance vs distance.
# Structural prediction if exchangeable-with-one-constraint (sum_{b!=0} eta_b = -n): Cov = -Var/(m-1), FLAT.
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f={};d=2
    while d*d<=x:
        while x%d==0:f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def periods(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    m=(p-1)//n
    reps=[pow(g,i,p) for i in range(m)]   # period indexed by multiplicative position i in Z_m
    eta=[sum(math.cos(2*math.pi*((r*x)%p)/p) for x in mu) for r in reps]
    return eta,m
print("Are Gauss periods log-correlated (FHK) or independent white-noise (iid-Gumbel)?",flush=True)
print(f"{'p':>9} {'n':>4} {'m':>6} {'Var':>7} {'-Var/(m-1)':>11} {'meanCov d>=1':>12} {'stdCov':>8} {'max|eta|/sqrt(n)':>16}",flush=True)
for p in range(17,200000):
    if not isprime(p): continue
    pm1=p-1;n=1
    while pm1%2==0: pm1//=2; n*=2
    if n<8 or n>32: continue
    m=pm1
    if m<13 or m>4000: continue
    if len(fac(m))<1: continue
    # pick a few prize-adjacent: p ~ n^4..n^5
    if not (n**3 < p < n**6): continue
    eta,m=periods(p,n)
    mu_mean=statistics.mean(eta); var=statistics.pvariance(eta)
    # cyclic autocovariance C(d) = mean_i (eta_i-mean)(eta_{i+d}-mean)
    C=[]
    for d in range(1,min(m,40)):
        s=sum((eta[i]-mu_mean)*(eta[(i+d)%m]-mu_mean) for i in range(m))/m
        C.append(s)
    pred=-var/(m-1)
    mx=max(abs(x) for x in eta)/math.sqrt(n)
    print(f"{p:>9} {n:>4} {m:>6} {var:>7.2f} {pred:>11.4f} {statistics.mean(C):>12.4f} {statistics.pstdev(C):>8.4f} {mx:>16.3f}",flush=True)
print("\nIf meanCov(d>=1) ~ -Var/(m-1) (tiny) and stdCov ~ 0 => FLAT/distance-independent => NOT log-correlated",flush=True)
print("=> periods are exchangeable white-noise (one sum-constraint), max = iid-Gumbel ~ sqrt(2n log m). Crown theory REFUTED.")
print("DONE")

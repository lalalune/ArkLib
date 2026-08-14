import math
# EVT angle: does the MARGINAL tail of eta_b/sqrt(n) match Gaussian out to the DEEP tail lambda~sqrt(2 log m)?
# If #{b:|eta_b|>lambda sqrt(n)} ~ m*e^{-lambda^2/2} all the way to the max, a union/Chernoff bound gives the
# floor M<=sqrt(2n log m) as an EVT theorem. If the deep tail is HEAVIER at structured primes, it's the wall.
def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%x==0:continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def v2(x):
    s=0
    while x%2==0:x//=2;s+=1
    return s
def fac(x):
    f={};dd=2
    while dd*dd<=x:
        while x%dd==0:f[dd]=f.get(dd,0)+1;x//=dd
        dd+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def periods(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    m=(p-1)//n;reps=[pow(g,i,p) for i in range(m)]
    return [sum(math.cos(2*math.pi*((r*x)%p)/p) for x in mu) for r in reps], m
for n,plo in [(32,1048576),(64,16777216)]:
    mu2=int(round(math.log2(n)));step=1<<mu2;p=(plo//step)*step+1
    while not((p-1)%n==0 and v2(p-1)>=mu2 and isprime(p)): p+=step
    eta,m=periods(p,n)
    sd=math.sqrt(n)
    Mx=max(abs(e) for e in eta)
    floor=math.sqrt(2*n*math.log(m))
    print(f"\nn={n} p={p} m={m}: max|eta|={Mx:.2f} floor=sqrt(2n log m)={floor:.2f} ratio={Mx/floor:.3f}",flush=True)
    print(f"  {'lambda':>7} {'#{|eta|>lam*sqrtn}':>16} {'Gauss m*e^-lam^2/2':>18} {'ratio(emp/Gauss)':>16}",flush=True)
    for lam in [2.0,2.5,3.0,3.5,4.0,4.5,5.0]:
        emp=sum(1 for e in eta if abs(e)>lam*sd)
        gauss=m*math.exp(-lam*lam/2)*2  # two-sided
        rat=emp/gauss if gauss>1e-9 else float('inf')
        print(f"  {lam:>7.1f} {emp:>16} {gauss:>18.2f} {rat:>16.2f}",flush=True)
    lammax=Mx/sd
    print(f"  deep tail: max lambda = {lammax:.2f}, sqrt(2 log m)={math.sqrt(2*math.log(m)):.2f} (Gumbel center)",flush=True)
print("\nIf emp/Gauss stays ~O(1) (not blowing up) to the deep tail => marginal subgaussian => EVT floor provable.",flush=True)
print("If emp/Gauss blows up at large lambda => heavy deep tail => the wall. DONE")

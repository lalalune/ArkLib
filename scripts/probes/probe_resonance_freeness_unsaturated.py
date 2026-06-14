import numpy as np, math, cmath
# HONEST re-test: is multi-factor favorability real, or an artifact of M saturating at its trivial cap n
# (which happens at n=2,4)? Measure the RESONANCE-FREENESS rho = M/sqrt(n log m) in a regime where n is
# moderate (16..64) so M ~ sqrt(n log m) << n is NOT saturated. If rho DECREASES with k (#prime factors
# of m) for unsaturated n => favorability is real. If rho is flat/noisy => the earlier signal was the
# saturation artifact and I over-claimed.
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
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
def Mres(p,n,m):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    # m can be large; sample up to 20000 cosets for the max (worst-case proxy)
    import random
    reps=[pow(g,i,p) for i in range(min(m,20000))]
    best=0.0
    for r in reps:
        s=0.0
        for x in mu: s+=math.cos(2*math.pi*((r*x)%p)/p)
        a=abs(s)
        if a>best:best=a
    return best
print("RESONANCE-FREENESS rho=M/sqrt(n log m) vs k=#prime factors of m, in UNSATURATED n in [16,64]",flush=True)
print(f"{'p':>10} {'n':>4} {'m':>9} {'k':>3} {'M':>8} {'sqrt(n logm)':>12} {'rho':>7}  factors",flush=True)
rows=[]
for p in range(17, 5_000_000):
    if not isprime(p):continue
    pm1=p-1;n=1
    while pm1%2==0: pm1//=2; n*=2
    m=pm1
    if n<16 or n>64: continue
    if m<7: continue
    k=len(fac(m))
    M=Mres(p,n,m)
    base=math.sqrt(n*math.log(m))
    rho=M/base
    rows.append((k,rho,p,n,m))
    print(f"{p:>10} {n:>4} {m:>9} {k:>3} {M:>8.3f} {base:>12.3f} {rho:>7.3f}  {dict(fac(m))}",flush=True)
    if len(rows)>=22: break
# correlation of rho with k
import statistics
byk={}
for k,rho,_,_,_ in rows: byk.setdefault(k,[]).append(rho)
print("\nmean resonance-freeness rho by k (#prime factors of m):",flush=True)
for k in sorted(byk): print(f"  k={k}: mean rho={statistics.mean(byk[k]):.3f}  (n={len(byk[k])})",flush=True)
ks=[r[0] for r in rows]; rs=[r[1] for r in rows]
if len(set(ks))>1:
    cc=np.corrcoef(ks,rs)[0,1]
    print(f"\ncorr(k, rho) = {cc:+.3f}  (negative => more factors LOWER resonance = favorable; ~0 => artifact)",flush=True)
print("DONE")

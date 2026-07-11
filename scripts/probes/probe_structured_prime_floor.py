import numpy as np, math
# DECISIVE in-regime test: at 2-power-STRUCTURED primes in the PRIZE regime (n ~ p^{1/4}, large 2-part),
# does the worst-case max M = max_{b!=0}|eta_b| EXCEED the floor sqrt(2 n log m), or stay below?
# M <= floor in-regime  => floor is the right delta* target (open problem = prove it).
# M >  floor in-regime  => the prize floor is WRONG at FFT primes; the true delta* is larger (discovery).
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
def v2(x):
    s=0
    while x%2==0: x//=2; s+=1
    return s
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
def maxM(p,n):
    g=proot(p); h=pow(g,(p-1)//n,p)
    mu=np.array([pow(h,i,p) for i in range(n)], dtype=np.int64)
    m=(p-1)//n
    reps=np.array([pow(g,i,p) for i in range(m)], dtype=np.int64)  # one rep per coset
    best=0.0
    CH=200000
    for s in range(0,m,CH):
        blk=reps[s:s+CH][:,None]                       # (b,1)
        prod=(blk*mu[None,:]) % p                       # (b,n)
        c=np.cos(2*math.pi*prod/p).sum(axis=1)          # (b,)
        a=np.abs(c).max()
        if a>best: best=a
    return best,m
print("In-regime structured-prime floor test: does M exceed floor sqrt(2 n log m)?",flush=True)
print(f"{'p':>12} {'v2(p-1)':>7} {'n':>5} {'m':>9} {'logp(n)':>8} {'M':>9} {'floor':>9} {'M/floor':>8} {'M/sqrtn':>8}",flush=True)
import sympy
for n in [32,64,128]:
    lo,hi = n**4, n**5
    cnt=0
    # scan for primes with 2-part EXACTLY divisible by n (structured), p in [n^4,n^5]
    # step through p = 1 + n*odd to force 2-part >= n... actually force v2(p-1)>=log2 n
    mu2=int(math.log2(n))
    step=1<<mu2
    start=((lo)//step)*step+1
    p=start
    while p<hi and cnt<3:
        p+=step
        if (p-1)%n!=0: continue
        if not isprime(p): continue
        if v2(p-1)<mu2: continue
        # prefer LARGE 2-part (structured): require v2 >= mu2 (>=) ; take a few
        M,m=maxM(p,n)
        floor=math.sqrt(2*n*math.log(m))
        logpn=math.log(p)/math.log(n)  # n = p^{1/logpn}; prize wants ~4
        print(f"{p:>12} {v2(p-1):>7} {n:>5} {m:>9} {logpn:>8.2f} {M:>9.3f} {floor:>9.3f} {M/floor:>8.3f} {M/math.sqrt(n):>8.3f}",flush=True)
        cnt+=1
print("\nM/floor <= 1 in-regime => floor is the correct delta* target. M/floor > 1 => floor VIOLATED at FFT primes.",flush=True)
print("DONE")

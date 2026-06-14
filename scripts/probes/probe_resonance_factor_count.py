import numpy as np, math, cmath
# Decisive test of the Gauss-reducibility attack surface: as the NUMBER of prime factors of m grows,
# does M(FFT subgroup) stay at the floor (Jacobi coupling saves it) or grow toward the tensor product
# prod R_i (reducibility overshoots)? If M/floor stays ~1 regardless of #factors => coupling is the key
# mechanism. If M/floor grows with #factors => the per-prime resonances multiply (bad).
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
def Mfft(p):
    pm1=p-1;n=1
    while pm1%2==0: pm1//=2; n*=2
    m=pm1
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    reps=[pow(g,i,p) for i in range(m)]
    eta=np.array([sum(cmath.exp(2j*math.pi*((r*x)%p)/p).real for x in mu) for r in reps])
    return n,m,np.abs(eta).max()
# find primes with m=oddpart having 1,2,3,4 distinct prime factors, m moderate
print("k=#distinct prime factors of m=oddpart(p-1) vs M/floor (does coupling hold M at floor as k grows?)",flush=True)
print(f"{'p':>8} {'n(2pt)':>7} {'m=odd':>7} {'k facs':>7} {'M':>8} {'floor':>8} {'M/floor':>8}",flush=True)
seen_k={}
for p in range(17, 200000):
    if not isprime(p):continue
    pm1=p-1;n=1
    while pm1%2==0: pm1//=2; n*=2
    m=pm1
    if m<3 or m>3000: continue
    k=len(fac(m))
    if seen_k.get(k,0)>=3: continue   # 3 examples per k
    n2,m2,M=Mfft(p)
    floor=math.sqrt(2*n*math.log(m))
    seen_k[k]=seen_k.get(k,0)+1
    print(f"{p:>8} {n:>7} {m:>7} {k:>7} {M:>8.3f} {floor:>8.3f} {M/floor:>8.3f}  ({dict(fac(m))})",flush=True)
    if all(seen_k.get(kk,0)>=3 for kk in [1,2,3,4]): break
print("\nIf M/floor ~ 1 for ALL k => Jacobi coupling holds the resonance at the floor regardless of #factors",flush=True)
print("(the key mechanism). If M/floor GROWS with k => the small-prime resonances multiply (reducibility hurts).",flush=True)
print("DONE")

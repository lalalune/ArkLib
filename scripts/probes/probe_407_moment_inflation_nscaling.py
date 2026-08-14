import numpy as np, math
# DECISIVE for M <= n^{1/2+o(1)}: is the moment inflation K_r = E_r/Wick n-INDEPENDENT (~c^r, ABSORBED =>
# n^{1/2+o(1)} provable) or n-DEPENDENT (~n^{delta r}, breaks it)? Compute K_r(n) at fixed depth r for
# n=16,32,64 (prize regime p~n^4) via exact r-fold FFT convolution, and report the n-scaling K_r(2n)/K_r(n).
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
def doublefact(r):
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v
def Kr(p,n,Rmax):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    d1=np.zeros(p)
    for x in mu: d1[x]+=1.0
    F1=np.fft.rfft(d1); Fr=F1.copy(); out={}
    for r in range(1,Rmax+1):
        if r>1: Fr=Fr*F1
        if r>=2:
            dr=np.fft.irfft(Fr,n=p)
            Er=float(np.sum(np.round(dr)**2))
            out[r]=Er/(doublefact(r)*(n**r))
    return out
def firstprime(n):
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1
    while True:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if isprime(p): return p
res={}
for n in [16,32,64]:
    p=firstprime(n); res[n]=Kr(p,n,14)
    print(f"n={n} p={p}: K_r = "+" ".join(f"{r}:{res[n][r]:.2f}" for r in [6,8,10,12,14]),flush=True)
print("\nn-scaling of K_r at FIXED r (K_r(2n)/K_r(n)):",flush=True)
for r in [8,10,12,14]:
    s1=res[32][r]/res[16][r]; s2=res[64][r]/res[32][r]
    print(f"  r={r}: K(32)/K(16)={s1:.2f}  K(64)/K(32)={s2:.2f}",flush=True)
print("\nIf K(2n)/K(n) -> 1 (bounded, n-independent) => inflation ~c^r ABSORBED => M<=n^{1/2+o(1)} PROVABLE via moments.",flush=True)
print("If K(2n)/K(n) grows ~2^{delta r} (n-dependent) => inflation ~n^{delta r} => breaks n^{1/2+o(1)}.",flush=True)
# also the actual moment bound exponent
print("\nMoment bound M<=(p E_r)^{1/2r} -> exponent log_n(bound):",flush=True)
for n in [16,32,64]:
    p=firstprime(n)
    best=min((p*res[n][r]*doublefact(r)*(n**r))**(1.0/(2*r)) for r in res[n])
    print(f"  n={n}: min_r (p E_r)^(1/2r) = {best:.2f} = n^{math.log(best)/math.log(n):.3f}  (n^0.5={math.sqrt(n):.2f})",flush=True)
print("DONE")

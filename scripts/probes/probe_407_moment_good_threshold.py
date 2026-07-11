import numpy as np, math
# Characterize the PRIME-DEPENDENT moment-method success: compute E_r(mu_n,F_p) EXACTLY to high depth via
# r-fold cyclic convolution (FFT), find the depth where E_r crosses Wick=(2r-1)!!n^r, and correlate with the
# count of short excess relations. Moment-good (never crosses by depth log m) => floor provable by moments for
# THAT prime. Tests whether the prize family contains moment-bad primes (=> family-level moment method fails).
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
def df1(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p);mu=[pow(h,i,p) for i in range(n)]
    d=np.zeros(p); 
    for x in mu: d[x]+=1.0
    return d
def doublefact(r): 
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v
def cross_depth(p,n,Rmax):
    d1=df1(p,n)
    F1=np.fft.rfft(d1)
    cross=None; ratios=[]
    Fr=F1.copy()
    for r in range(1,Rmax+1):
        if r>1: Fr=Fr*F1
        if r>=2:
            dr=np.fft.irfft(Fr, n=p)
            Er=float(np.sum(np.round(dr)**2))   # E_r = sum d_r(v)^2
            wick=doublefact(r)*(n**r)
            ratio=Er/wick
            ratios.append((r,ratio))
            if ratio>1 and cross is None: cross=r
    return cross, ratios
print("Prime-dependent moment-method success (E_r vs Wick) at n=16,32 prize-regime primes (p~n^4):",flush=True)
for n in [16,32]:
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1; cnt=0; logm0=None
    print(f"\n--- n={n} ---",flush=True)
    while cnt<5 and p<3*lo:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if not isprime(p): continue
        m=(p-1)//n; depth=math.log(m)   # moment optimal depth ~ ln m
        cross,ratios=cross_depth(p,n,14)
        tail=" ".join(f"{r}:{ratio:.2f}" for r,ratio in ratios if r>=6)
        verdict = "MOMENT-GOOD (no cross<=14)" if cross is None else (f"crosses r={cross}, depth~{depth:.0f} => "+("BAD (cross<=depth)" if cross<=depth else "good (cross>depth)"))
        print(f"  p={p} m={m} lnm={depth:.1f}: {verdict}   [r>=6: {tail}]",flush=True)
        cnt+=1
print("\nIf ALL prize primes are moment-good => moment method proves floor for the family (closure path!).",flush=True)
print("If some cross within depth => family-level moment method fails (need direct BGK). DONE")

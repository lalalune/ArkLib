import numpy as np
from math import log,sqrt,lgamma,exp
def gauss_abs(p,n):
    pm1=p-1
    def factor(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    fs=factor(pm1);g=2
    while not all(pow(g,pm1//q,p)!=1 for q in fs):g+=1
    h=pow(g,pm1//n,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.float64)
    b=np.arange(1,p,dtype=np.float64)
    ang=2*np.pi*np.outer(b,mu)/p
    return np.abs(np.cos(ang).sum(1)+1j*np.sin(ang).sum(1))

# In-regime: n ~ p^{1/4}..p^{1/5}.  Fix n=16, grow p so n/sqrt(p) shrinks. Track first Wick violation depth.
print("n=16 fixed, growing p (n/sqrt(p) shrinking): depth k where E_k first exceeds (2k-1)!! n^k")
# need n | p-1, p prime. n=16.
def primes_with(n, lo, hi, want):
    out=[]
    c=lo - lo%n +1
    while c<hi and len(out)<want:
        # c ≡ 1 mod n
        if c>2:
            isp=all(c%d for d in range(2,int(c**.5)+1))
            if isp and (c-1)%n==0: out.append(c)
        c+=n
    return out
for n in [16,32]:
    print(f"--- n={n} ---")
    for p in primes_with(n, n*n//2, 200000, 60)[::8]:
        a=gauss_abs(p,n);a2=a**2.0
        firstviol=None;maxk=int(log(p))+1
        for k in range(2,maxk):
            wick=exp(lgamma(2*k+1)-k*log(2)-lgamma(k+1))*n**k
            Ek=(a2**k).sum()/p+n**(2*k)/p
            if Ek>wick: firstviol=k;break
        M=a.max();prize=sqrt(n*log(p/n))
        print(f" p={p:6} n/sqrt(p)={n/sqrt(p):.3f} 1stWickViol@k={firstviol} logp={log(p):.1f} M/prize={M/prize:.3f}")

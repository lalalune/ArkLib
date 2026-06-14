#!/usr/bin/env python3
"""
PROXIMITY PRIZE -- Conjecture (G), the ONE open link.  FIND the depth r where
F_p-GENUINE relations first appear and characterize them.  Meet-in-the-middle so we can
reach the threshold for n=8 (p~512..4096) and n=16 (p~4096).

A genuine relation: (x_1..x_r,y_1..y_r) in mu_n^{2r}, sum x_i == sum y_j (mod p),
but alpha = sum zeta^{a_i} - sum zeta^{b_j} != 0 in Z[zeta_n] (n=2^mu => Z[x]/(x^{n/2}+1)).

MITM: build all r-multisets-with-order of exponents on the x-side; key each by its
mod-p sum S; store the cyclotomic vector. Then for the y-side iterate and look up S.
We only need to MATCH the mod-p sum and then test alpha. To make it tractable we bucket
x-tuples by mod-p sum into a dict S -> list of (cyc-vec). For each y-tuple (same count),
we look up S=sum and for each stored x with the same S compute alpha = xvec - yvec; if
nonzero -> genuine.  We can also collapse by dilation gauge a_1=0 to cut a factor of n.

Counts: ordered tuples.  We report G_r, suppression vs n^{2r}/p, and structure of alpha.
"""
import itertools, math, cmath
from collections import defaultdict

def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    d=3
    while d*d<=q:
        if q%d==0: return False
        d+=2
    return True
def factor(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError
def find_prime(t,mod):
    p=t+((1-(t%mod))%mod)
    if p<t:p+=mod
    while not isprime(p):p+=mod
    return p

def cyc_vec_from_counts(cnt, phi, n):
    """cnt: dict exponent(0..n-1)->signed multiplicity. reduce to length-phi vector."""
    v=[0]*phi
    for k,c in cnt.items():
        kk=k%n
        if kk<phi: v[kk]+=c
        else:      v[kk-phi]-=c
    return tuple(v)

def cyc_norm(vec, phi, n):
    prod=1.0+0j; mx=0.0
    for j in range(1,n,2):
        w=cmath.exp(2j*math.pi*j/n)
        val=sum(vec[k]*(w**k) for k in range(phi))
        prod*=val; a=abs(val); mx=max(mx,a)
    return round(prod.real), mx

def threshold(n, p, rmax, g=None):
    if g is None: g=primroot(p)
    z=pow(g,(p-1)//n,p); zpow=[pow(z,k,p) for k in range(n)]
    phi=n//2; m=(p-1)//n
    beta=math.log(p)/math.log(n)
    print(f"\n{'='*78}\nn={n} p={p} beta={beta:.2f} m={m} log2m={math.log2(m):.1f}\n{'='*78}",flush=True)
    for r in range(2,rmax+1):
        # x-side: dict S(mod p) -> list of cyc-vec (as tuple of length-n exponent counts is heavy;
        # store the reduced length-phi vector directly).  Use dilation gauge: fix a_1=0.
        # number of x-tuples with a_1=0: n^{r-1}.
        xbuckets=defaultdict(list)
        for tail in itertools.product(range(n),repeat=r-1):
            ax=(0,)+tail
            S=sum(zpow[a] for a in ax)%p
            cnt=defaultdict(int)
            for a in ax: cnt[a]+=1
            xbuckets[S].append((cnt, ax))
        # y-side: iterate over ALL y-tuples (n^r), look up S.
        gen=0; char0=0; tot=0
        norms=defaultdict(int); maxabs=defaultdict(int); minabsN=None
        canon=set(); examples=[]
        for by in itertools.product(range(n),repeat=r):
            S=sum(zpow[b] for b in by)%p
            lst=xbuckets.get(S)
            if not lst: continue
            ycnt=defaultdict(int)
            for b in by: ycnt[b]+=1
            for (xcnt,ax) in lst:
                tot+=1
                d=defaultdict(int)
                for k,c in xcnt.items(): d[k]+=c
                for k,c in ycnt.items(): d[k]-=c
                vec=cyc_vec_from_counts(d,phi,n)
                if all(c==0 for c in vec):
                    char0+=1
                else:
                    gen+=1
                    N,mx=cyc_norm(vec,phi,n)
                    norms[N]+=1; maxabs[round(mx,2)]+=1
                    if minabsN is None or abs(N)<minabsN: minabsN=abs(N)
                    # dilation canonical (gauge already a_1=0 on x; canonicalize jointly)
                    best=None
                    for s in range(n):
                        c=(tuple((a+s)%n for a in ax),tuple((b+s)%n for b in by))
                        if best is None or c<best: best=c
                    canon.add(best)
                    if len(examples)<6: examples.append((ax,by,vec,N,round(mx,3)))
        # the gauge fixed a_1=0 so we counted 1/n of the dilation orbit on the x-side.
        # full ordered genuine count = gen * n (restore dilation on x).  (y-side already full.)
        gen_full=gen*n; char0_full=char0*n; tot_full=tot*n
        rate=n**(2*r)/p
        print(f"\n r={r}: gauged total={tot} char0={char0} GENUINE={gen} "
              f"(full: G_r={gen_full}, char0={char0_full})  naive n^2r/p={rate:.1f}",flush=True)
        if gen==0:
            print(f"    --> G_r=0 (suppressed). need genuine to appear by r~log2 m={math.log2(m):.0f}",flush=True)
            continue
        print(f"    suppression G_r/(n^2r/p) = {gen_full/rate:.4f}  #dilation-orbits(gauged)={len(canon)}",flush=True)
        nz=sorted(norms.items())
        print(f"    Norm(alpha) hist {{val:gauged-count}}: {dict(nz[:12])}{' ...' if len(nz)>12 else ''}",flush=True)
        alldiv=all(N%p==0 for N in norms if N!=0)
        print(f"    all |Norm(alpha)| divisible by p? {alldiv}  min|Norm|={minabsN} (={minabsN//p if minabsN and minabsN%p==0 else '?'}*p? ratio {minabsN/p:.4g})",flush=True)
        mh=sorted(maxabs.items())
        print(f"    max|conj alpha| hist: {dict(mh[:8])}{' ...' if len(mh)>8 else ''}",flush=True)
        for (ax,by,vec,N,mx) in examples[:4]:
            print(f"      x={list(ax)} y={list(by)} alpha={list(vec)} N={N} maxconj={mx}",flush=True)

if __name__=="__main__":
    # push n=8 to the threshold. n^{r} y-loop * avg-bucket. for n=8 r up to 6 (8^6=262144 y-loop,
    # x-buckets 8^5=32768) is fast.
    threshold(8, find_prime(8**3, 8), 7)    # p~521 beta3
    threshold(8, find_prime(8**4, 8), 7)    # p~4129 beta4
    threshold(8, find_prime(8**5, 8), 7)    # p~32771? beta5 (deep, genuine very rare)
    threshold(16, find_prime(16**3,16), 5)  # p~4129 beta3
    threshold(16, find_prime(16**4,16), 4)  # p~65537 beta4

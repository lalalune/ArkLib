#!/usr/bin/env python3
"""#407 CRACK 7 / EVT validation (prize regime, untried): does the Gauss-period MAX follow the
i.i.d.-Gaussian extreme-value scale M ~ sqrt(2n log m) (=> CRACK 7 closes at C=sqrt2), or is it
SUB-EVT (M < sqrt(2n log m), floor even safer)? m=(p-1)/n = number of periods. EVT max of m i.i.d.
N(0,n) is ~sqrt(2n log m). Sweep GROWING m at fixed n; track R2 = M/sqrt(2n log m)."""
import numpy as np
from sympy import isprime
def Mmax(p,n):
    fac=set();x=p-1;d=2
    while d*d<=x:
        while x%d==0:fac.add(d);x//=d
        d+=1
    if x>1:fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac):g+=1
    h=pow(g,(p-1)//n,p);ind=np.zeros(p);cur=1
    for _ in range(n):ind[cur]=1.0;cur=cur*h%p
    F=np.abs(np.fft.rfft(ind));F[0]=-1.0;return F.max()
print(f"{'n':>4} {'p':>9} {'m=(p-1)/n':>10} {'log2 m':>7} {'M':>8} {'sqrt(2n ln m)':>13} {'R2=M/that':>10}")
print("-"*68)
for n in [16,32,64]:
    R2s=[]
    # sweep p with growing m: p = n*m+1 prime, m from small to large
    targets=[]
    m=3
    while len(targets)<7 and m< 8_000_000//n:
        p=n*m+1
        if isprime(p): targets.append((m,p))
        m=int(m*2.4)+1
    for m,p in targets:
        M=Mmax(p,n); scale=np.sqrt(2*n*np.log(m)); R2=M/scale
        R2s.append((np.log2(m),R2))
        print(f"{n:>4} {p:>9} {m:>10} {np.log2(m):>7.1f} {M:>8.2f} {scale:>13.2f} {R2:>10.4f}")
    if len(R2s)>=2:
        sl=np.polyfit([a for a,_ in R2s],[b for _,b in R2s],1)[0]
        print(f"     -> n={n}: R2 trend vs log2 m: slope={sl:+.4f}  ({'->1 EVT-iid' if abs(R2s[-1][1]-1)<0.1 else 'sub-EVT (<1, floor safer)' if R2s[-1][1]<0.9 else 'near-EVT'})")
    print()
print("EVT(CRACK7): R2->1 => floor = sqrt(2n log m) exactly (C=sqrt2). R2<1 & flat/decreasing =>")
print("periods are SUB-iid-extreme (more concentrated than i.i.d. Gaussian) => floor strictly safer than EVT bound.")

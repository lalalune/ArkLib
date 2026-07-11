#!/usr/bin/env python3
"""#407: effective sup-norm exponent alpha(m) = d log M / d log n at FIXED index m.
Floor M<=C sqrt(n log m) => alpha = 1/2. BGK degradation => alpha creeps above 1/2 as m grows.
Measure alpha(m) for a ladder of fixed m; find where/if it crosses 1/2 (the crux)."""
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
print(f"{'m':>7} {'#pts':>4} {'n-range':>16} {'alpha=dlogM/dlogn':>18} {'M/sqrt(n) trend':>22}")
print("-"*74)
for m in [2,4,8,16,64,256,1024,4096,16384]:
    pts=[]
    for mu in range(2,20):
        n=1<<mu;p=n*m+1
        if p>9_000_000:break
        if not isprime(p):continue
        pts.append((n,Mmax(p,n)))
    if len(pts)<2:continue
    ln=np.array([np.log(n) for n,_ in pts]);lM=np.array([np.log(M) for _,M in pts])
    alpha=np.polyfit(ln,lM,1)[0]
    msqrt=[round(M/np.sqrt(n),3) for n,M in pts]
    flag="  <- alpha>0.5 (BGK degrades)" if alpha>0.505 else ("  (sub-floor)" if alpha<0.495 else "  (~floor)")
    print(f"{m:>7} {len(pts):>4} {str((pts[0][0],pts[-1][0])):>16} {alpha:>18.4f} {str(msqrt):>22}{flag}")
print("\nCRUX: if alpha(m) monotonically increases with m and is heading >0.5 by m~2^12-2^14,")
print("that quantifies BGK degradation toward the prize m=2^128 (floor in danger).")
print("If alpha(m) stays <=0.5 even at the largest reachable m, the floor is robust at constant index.")

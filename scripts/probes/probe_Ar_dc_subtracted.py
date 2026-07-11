"""
CORRECT object: A_r = E_r(F_p) - n^{2r}/p  (DC-subtracted). Does A_r/Wick -> 0 (the real favorable signal)?
The raw E_r/Wick is vacuous (DC term n^{2r}/p dominates at deep r when p~n^4). Recompute with subtraction.
"""
from collections import Counter
import math
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
def Er(p,n,R):
    c=Counter({0:1}); E={}; S=subgroup(p,n)
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc; E[r]=sum(m*m for m in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
print("A_r = E_r(F_p) - n^{2r}/p  (DC-subtracted); ratio A_r/Wick. Does A_r/Wick decay (real signal)?")
for n,p in [(16,65537),(32,1048609),(32,1048721)]:
    R=min(2*n-2,13)
    E=Er(p,n,R)
    print(f" n={n} p={p} (p/n^4={p/n**4:.3f}):")
    print(f"   {'r':>2} {'E_r/Wick':>9} {'DC/Wick':>9} {'A_r/Wick':>9} {'A_r<=Wick?':>10}")
    for r in range(2,R+1):
        wick=dfac(r)*n**r
        dc=n**(2*r)/p
        Ar=E[r]-dc
        print(f"   {r:>2} {E[r]/wick:>9.4f} {dc/wick:>9.4f} {Ar/wick:>9.4f} {str(Ar<=wick):>10}")
print()
print("=> A_r/Wick is the REAL object. If A_r/Wick<=1 (decreasing) at deep r -> prize favorable.")
print("   Raw E_r/Wick rising was the DC artifact. The DC term n^{2r}/p IS the eta_0=n DC contribution.")

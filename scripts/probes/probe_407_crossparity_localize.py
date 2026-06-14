#!/usr/bin/env python3
"""
Where does the POSITIVE cross-parity (amplification) localize?
Aggregate sum_{b!=0} X = -n^2/2 (suppressing). But worst single-b X can be > 0.
QUESTION (the task's odd-part core): is the positive part
   X^+ := sum_{b!=0, X(b)>0} X(b)
confined to O(log n) freqs, and how does max_b X(b) scale?
Also: split b by 2-adic valuation v_2 of the 'direction' to test imprimitivity link.
"""
import cmath, math
def isprime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prim_root_order(n,p):
    e=(p-1)//n
    for a in range(2,p):
        g=pow(a,e,p)
        if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: return g
    raise RuntimeError
def periods(H,p):
    w=2j*math.pi/p
    return [sum(cmath.exp(w*((b*x)%p)) for x in H) for b in range(p)]
def analyze(n,p):
    g=prim_root_order(n,p); zeta=g
    Hk1=[pow(g,2*j,p) for j in range(n//2)]
    P1=periods(Hk1,p)
    X=[0.0]*p
    for b in range(p):
        X[b]=2.0*(P1[b]*P1[(b*zeta)%p].conjugate()).real
    nz=range(1,p)
    Xpos=[X[b] for b in nz if X[b]>1e-9]
    Xneg=[X[b] for b in nz if X[b]<-1e-9]
    sumpos=sum(Xpos); sumneg=sum(Xneg)
    maxX=max(X[b] for b in nz); minX=min(X[b] for b in nz)
    # heavy positive: X >= n  (a single freq carrying >= n worth of alignment)
    heavy=[b for b in nz if X[b]>=n]
    print(f"n={n:3d} p={p:5d}: sum X={sumpos+sumneg:+.1f}(=-n^2/2={-(n*n)//2}) | "
          f"#pos={len(Xpos)} sum+={sumpos:.1f} | #neg={len(Xneg)} sum-={sumneg:.1f}")
    print(f"          maxX={maxX:.2f} (n={n}, 2n={2*n}) minX={minX:.2f}  "
          f"#{{X>=n}}={len(heavy)} (log2 p={math.log2(p):.1f})")
    return len(heavy), maxX, n
for n in [8,16,32,64]:
    cnt=0
    for p in range(n+1,9000):
        if (p-1)%n==0 and isprime(p):
            analyze(n,p); cnt+=1
            if cnt>=3: break
    print()

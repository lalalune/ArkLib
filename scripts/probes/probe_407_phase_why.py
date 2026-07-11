#!/usr/bin/env python3
"""WHY is cos01@b* ~ +-1 (real-collinear) almost always? Test the structural
hypothesis: at b*, S0 and S1 are REAL multiples of a common phase, i.e. the
worst frequency makes both half-coset sums collinear. Is this true for ALL b
(structural), or special to b*? And what distinguishes the rare -1?"""
import numpy as np
from numpy.fft import fft
def gen(p):
    fac=set(); x=p-1; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac): g+=1
    return g
def subgroup(p,n):
    g=gen(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def study(p,n):
    H=subgroup(p,n)
    if len(set(H))!=n or n%2: return
    sq=sorted({(x*x)%p for x in H}); sqset=set(sq)
    rep=next(x for x in H if x not in sqset)
    coset1=sorted({(rep*x)%p for x in sq})
    w=-2*np.pi/p
    def S(setx,b): return sum(np.exp(1j*w*((b*x)%p)) for x in setx)
    ind=np.zeros(p)
    for x in H: ind[x]=1.0
    F=np.abs(fft(ind)); F[0]=-1; bstar=int(np.argmax(F))
    # how many b (over a sample) give |cos01|~1 (collinear)?
    coll=0; tot=0; cosvals=[]
    for b in range(1,min(p,600)):
        A=S(sq,b); B=S(coset1,b)
        if abs(A)>1e-9 and abs(B)>1e-9:
            tot+=1; c=(A*np.conj(B)).real/(abs(A)*abs(B)); cosvals.append(c)
            if abs(c)>0.999: coll+=1
    A=S(sq,bstar); B=S(coset1,bstar)
    cstar=(A*np.conj(B)).real/(abs(A)*abs(B))
    # check: is S1(b) = conj-rotation of S0? Note coset1 = rep*sq, so
    # S1(b)=sum e_p(b*rep*x) over x in sq = S0(b*rep). So cos01(b)=cos between S0(b),S0(b*rep).
    print(f"p={p:>7} n={n:>5} b*={bstar:>6} cos01@b*={cstar:>7.3f} collinear|cos|>.999: {coll}/{tot} meanabs={np.mean(np.abs(cosvals)):.3f}")

print("Structural note: coset1=rep*sq, so S1(b)=S0(rep*b). cos01(b)=cos angle(S0(b),S0(rep*b)).")
for (p,a) in [(257,3),(1153,4),(12289,5),(40961,6)]:
    study(p,2**a)
print("--- thick ---")
for p,n in [(257,128),(1153,576),(12289,6144),(40961,20480)]:
    study(p,n)

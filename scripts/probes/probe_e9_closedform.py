from fractions import Fraction as Fr
from math import factorial
from itertools import product
from collections import Counter
import numpy as np
r=9
fc=[Fr(1,factorial(k)**2) for k in range(r+1)]
def tmul(a,b):
    o=[Fr(0)]*(r+1)
    for i in range(r+1):
        if a[i]==0:continue
        for j in range(r-i+1):
            if b[j]!=0:o[i+j]+=a[i]*b[j]
    return o
def Egf(m):
    res=[Fr(0)]*(r+1);res[0]=Fr(1);b=fc[:];e=m
    while e>0:
        if e&1:res=tmul(res,b)
        e>>=1
        if e>0:b=tmul(b,b)
    v=res[r]*factorial(2*r);assert v.denominator==1;return v.numerator
def Ebrute(m):
    d=m;verts=[]
    for j in range(d):
        v=[0]*d;v[j]=1;verts.append(v)
        v=[0]*d;v[j]=-1;verts.append(v)
    verts=np.array(verts,dtype=np.int64);cnt=Counter()
    for tup in product(range(2*d),repeat=r):
        s=verts[list(tup)].sum(0);cnt[s.tobytes()]+=1
    return sum(v*v for v in cnt.values())
print("=== verify GF vs brute r=9 n=2,4 ===")
for n in [2,4]:
    m=n//2;g=Egf(m);bf=Ebrute(m);print(f"n={n}: GF={g} brute={bf} MATCH={g==bf}")
ns=list(range(2,44,2));vals=[Egf(n//2) for n in ns]
def fit(xs,ys,deg):
    N=deg+1;M=[[Fr(xs[i])**j for j in range(N)]+[Fr(ys[i])] for i in range(N)]
    for c in range(N):
        p=next(rr for rr in range(c,N) if M[rr][c]!=0);M[c],M[p]=M[p],M[c]
        pv=M[c][c];M[c]=[x/pv for x in M[c]]
        for rr in range(N):
            if rr!=c and M[rr][c]!=0:
                f=M[rr][c];M[rr]=[M[rr][k]-f*M[c][k] for k in range(N+1)]
    return [M[i][N] for i in range(N)]
co=fit(ns[:10],vals[:10],9)
print("=== E_9 coeffs a0..a9 ===")
for j,c in enumerate(co):print(f"  n^{j}: {c}")
print("all int:",all(c.denominator==1 for c in co))
def ev(co,n):return sum(c*Fr(n)**j for j,c in enumerate(co))
ok=all(ev(co,n)==v for n,v in zip(ns,vals))
print("OVER-DET ALL MATCH (n=2..42):",ok)
print("a9=17!!=34459425:",co[9]==34459425," a8=-C(9,2)*17!!:",co[8]==-36*34459425)
print("E9(2)=",vals[0]," C(18,9)=",factorial(18)//(factorial(9)**2))

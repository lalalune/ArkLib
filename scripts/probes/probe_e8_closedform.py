from fractions import Fraction as Fr
from math import factorial
import numpy as np
from itertools import product
from collections import Counter

r = 8
fcoeffs=[Fr(1,factorial(k)**2) for k in range(r+1)]
def trunc_mul(a,b,r):
    out=[Fr(0)]*(r+1)
    for i in range(r+1):
        if a[i]==0:continue
        for j in range(r-i+1):
            if b[j]!=0: out[i+j]+=a[i]*b[j]
    return out
def E_gf(m,r):
    res=[Fr(0)]*(r+1);res[0]=Fr(1);b=fcoeffs[:];e=m
    while e>0:
        if e&1:res=trunc_mul(res,b,r)
        e>>=1
        if e>0:b=trunc_mul(b,b,r)
    v=res[r]*factorial(2*r);assert v.denominator==1;return v.numerator

def E_brute(m,r):
    d=m
    verts=[]
    for j in range(d):
        v=[0]*d;v[j]=1;verts.append(v)
        v=[0]*d;v[j]=-1;verts.append(v)
    verts=np.array(verts,dtype=np.int64) # (2d, d)
    cnt=Counter()
    for tup in product(range(2*d),repeat=r):
        s=verts[list(tup)].sum(0)
        cnt[s.tobytes()]+=1
    return sum(v*v for v in cnt.values())

print("=== VERIFY GF vs brute (r=8), n=2,4,6 ===")
for n in [2,4,6]:
    m=n//2;g=E_gf(m,r);bf=E_brute(m,r)
    print(f"n={n}: GF={g} brute={bf} MATCH={g==bf}")

ns=list(range(2,40,2))
vals=[E_gf(n//2,r) for n in ns]
print("=== E_8 GF values ==="); 
for n,v in zip(ns,vals):print(f"n={n}: {v}")

def fit_poly(xs,ys,deg):
    N=deg+1
    M=[[Fr(xs[i])**j for j in range(N)]+[Fr(ys[i])] for i in range(N)]
    for col in range(N):
        piv=next(rr for rr in range(col,N) if M[rr][col]!=0)
        M[col],M[piv]=M[piv],M[col]
        pv=M[col][col];M[col]=[x/pv for x in M[col]]
        for rr in range(N):
            if rr!=col and M[rr][col]!=0:
                f=M[rr][col];M[rr]=[M[rr][k]-f*M[col][k] for k in range(N+1)]
    return [M[i][N] for i in range(N)]

xs=ns[:9];ys=vals[:9]
coeffs=fit_poly(xs,ys,8)
print("=== fitted degree-8 poly coeffs a0..a8 ===")
for j,c in enumerate(coeffs):print(f"  n^{j}: {c}")
# verify all coeffs are integers
allint=all(c.denominator==1 for c in coeffs)
print("all integer coeffs:",allint)
# over-determined check: predict at extra points n=20,22,...,38
print("=== over-det check (fit must reproduce GF at extra n) ===")
def evalp(coeffs,n):return sum(c*Fr(n)**j for j,c in enumerate(coeffs))
ok=True
for n,v in zip(ns,vals):
    pv=evalp(coeffs,n)
    m=(pv==v)
    if not m: ok=False
    if n>=18: print(f"n={n}: fit={pv} gf={v} match={m}")
print("OVER-DET ALL MATCH:",ok)
# leading coeff should be (2r-1)!! = 15!! = 2027025
print("leading a8 =",coeffs[8]," expected 15!!=2027025:",coeffs[8]==2027025)
# second coeff law: -C(r,2)*(2r-1)!! = -C(8,2)*2027025 = -28*2027025
print("a7 =",coeffs[7]," expected -28*2027025 =",-28*2027025,":",coeffs[7]==-28*2027025)

#!/usr/bin/env python3
"""Batch 5: k-fold sumsets at correct degree, E_5 leading/subleading check, shift family,
and the first MCA-census closed forms (connecting to delta* directly)."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import isprime, big_prime_pow, mu, energyR, Zk_count, test_conjecture, SURVIVORS, DEAD
import itertools
from fractions import Fraction

def fit_poly(xs,ys,deg):
    A=[[Fraction(x)**j for j in range(deg+1)] for x in xs[:deg+1]]; b=[Fraction(y) for y in ys[:deg+1]]
    M=[A[i][:]+[b[i]] for i in range(deg+1)]; nn=deg+1
    for c in range(nn):
        piv=next(r for r in range(c,nn) if M[r][c]!=0); M[c],M[piv]=M[piv],M[c]
        inv=Fraction(1)/M[c][c]; M[c]=[v*inv for v in M[c]]
        for r in range(nn):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(nn+1)]
    return [M[i][nn] for i in range(nn)]
def polystr(coef):
    t=[]
    for i in range(len(coef)-1,-1,-1):
        if coef[i]!=0: t.append(f"({coef[i]})n^{i}" if i>0 else f"({coef[i]})")
    return " + ".join(t) or "0"
def Gp(n,power): p=big_prime_pow(n,power); return mu(p,n),p

# --- k-fold sumset at CORRECT degree k ---
def ksumset(m,k):
    n=1<<m; G,p=Gp(n,k+2); cur={0}
    for _ in range(k): cur={(a+b)%p for a in cur for b in G}
    return len(cur)
for k in [3,4]:
    pts=list(range(2,2+k+2))  # enough points for degree k (+verify)
    ns=[1<<m for m in pts]; ys=[ksumset(m,k) for m in pts]
    coef=fit_poly(ns[:k+1],ys[:k+1],k)
    pred=sum(coef[i]*Fraction(ns[-1])**i for i in range(k+1))
    if pred==ys[-1]:
        test_conjecture(f"K{k}",f"|{k}·μ_n| = {polystr(coef)}",
            lambda m,cc=coef,kk=k:(lambda n:sum(cc[i]*Fraction(n)**i for i in range(kk+1)))(1<<m),
            lambda m,kk=k:ksumset(m,kk), pts,"NOVEL-sumset")
    else:
        print(f"K{k} deg-{k} fit unverified: {list(zip(ns,ys))}")

# --- E_5 leading/subleading vs C9/C14 prediction (945, -9450) ---
def Er_clean(m,r):
    n=1<<m; G,p=Gp(n,r+1); return energyR(G,p,r)
e5pts=[1,2,3,4,5]; ns5=[1<<m for m in e5pts]; e5=[Er_clean(m,5) for m in e5pts]
# fit degree 5 using constant=0 constraint: solve for c1..c5 from 5 points (n, n^2..n^5)
A=[[Fraction(ns5[i])**j for j in range(1,6)] for i in range(5)]; b=[Fraction(e5[i]) for i in range(5)]
M=[A[i][:]+[b[i]] for i in range(5)]
for c in range(5):
    piv=next(r for r in range(c,5) if M[r][c]!=0); M[c],M[piv]=M[piv],M[c]
    inv=Fraction(1)/M[c][c]; M[c]=[v*inv for v in M[c]]
    for r in range(5):
        if r!=c and M[r][c]!=0: f=M[r][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(6)]
coef5=[Fraction(0)]+[M[i][5] for i in range(5)]  # c0=0, c1..c5
print("E5 fitted coeffs c0..c5:",[str(c) for c in coef5])
def dblfact(k):
    r=1
    while k>0: r*=k; k-=2
    return r
print(f"E5 leading (n^5): {coef5[5]} vs (2*5-1)!!={dblfact(9)}; subleading {coef5[4]} vs -(945)*C(5,2)={-945*10}")
# emit as conjecture if matches
if coef5[5]==dblfact(9) and coef5[4]==-945*10:
    test_conjecture("C9b","E_5 leading=945=(9!!) and subleading=-9450=-945*C(5,2) (confirms C9,C14 at r=5)",
        lambda x:True, lambda x:True, [1,2,3], "NOVEL-confirm")

# --- shift family: #{c in μ_n : c+s in μ_n} for s in a coset; conjecture 0 for s != special ---
def shift_count(m, s_mode):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    if s_mode=='one': s=1
    elif s_mode=='gen': s=G[1]+G[1]  # 2*g, a 'sum' shift
    return sum(1 for c in G if (c+s)%p in S)
# C16: #{c in μ_n: c+1 in μ_n} = 0
test_conjecture("C16","#{c∈μ_n: c+1∈μ_n} = 0 (no two roots differ by 1)",
    lambda m:0, lambda m:shift_count(m,'one'), [1,2,3,4,5],"NOVEL")
# C17: #{c in μ_n: c + 2g in μ_n} = 1 where 2g... test the structure (the diagonal 2a hits)
# actually #{c: c+t in μ_n} = |μ_n cap (μ_n - t)|; for t=2a (a in μ_n) this is >=1 (c=-a works:
#   -a + 2a = a in μ_n). Conjecture =1 generically (only c=-a). 
def shift_2a(m):
    n=1<<m; G,p=Gp(n,3); S=set(G); a=G[1]; t=(2*a)%p
    return sum(1 for c in G if (c+t)%p in S)
test_conjecture("C17","|μ_n ∩ (μ_n - 2a)| = 1 for a∈μ_n (only c=-a)",
    lambda m:1, shift_2a, [2,3,4,5],"NOVEL")

print("\n==== BATCH 5 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")

#!/usr/bin/env python3
"""Batch 4: a SYSTEMATIC generator. For each quantity family it fits an exact closed form on
small instances and VERIFIES on an independent larger one; survivors are emitted as conjectures."""
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
    terms=[]
    for i in range(len(coef)-1,-1,-1):
        c=coef[i]
        if c==0: continue
        terms.append(f"{c}n^{i}" if i>0 else f"{c}")
    return " + ".join(terms) if terms else "0"

def Gp(n, power): 
    p=big_prime_pow(n, power); return mu(p,n), p

# --- Family 1: even moments E_5 closed form (degree 5 poly) ---
def Er_clean(m,r):
    n=1<<m; G,p=Gp(n,r+1); return energyR(G,p,r)
# E_5: fit on n=2,4,8,16,32,64 (deg 5 needs 6 pts), verify... n^5 for 64 = 10^9 too slow.
# use n=2..32 (5 pts) for deg-5? need 6. Use n=2,4,8,16 + the structure. E_5 deg5 needs 6 pts.
# compute n=2,4,8,16,32 (5) + 64 (n^5=1e9 slow). Limit deg via known: E_5 deg 5.
e5pts=[1,2,3,4]  # n=2,4,8,16  (n^5=1M for 16, ok; 32^5=3e7 ok; 64 too slow)
e5pts=[1,2,3,4,5]  # add n=32 (3e7, ~30s)
ns5=[1<<m for m in e5pts]; e5=[Er_clean(m,5) for m in e5pts]
print("E5 data:", list(zip(ns5,e5)))
# deg-5 needs 6 points; we have 5 -> can't uniquely fit+verify. Fit deg-5 with 6 pts:
# add n=64 only if feasible; else conjecture leading coeff (2*5-1)!!=945 and report partial.
import math
# Family 1b: leading coeff conjecture extended r=5 -> 945, subleading -945*C(5,2)=-945*10=-9450
# verify leading via fit deg-5 needs 6 pts; instead check E_5(n)/n^5 trend + use 6th pt n=64 cheaply
# via histogram of 4-fold sums (n^4) then count -sum hits (n) -> Z_10? no. E_5 = n^5 build. skip 64.

# --- Family 2: k-fold sumset sizes |k·μ_n| = |{x_1+...+x_k : x_i in μ_n}| ---
def ksumset(m,k):
    n=1<<m; G,p=Gp(n, k+1)
    cur={0}
    for _ in range(k):
        cur={(a+b)%p for a in cur for b in G}
    return len(cur)
for k in [2,3,4]:
    pts=[2,3,4,5]; ns=[1<<m for m in pts]; ys=[ksumset(m,k) for m in pts]
    # fit deg-2 (sumsets ~ n^2/2-ish) ; verify on n=64 (m=6)
    try:
        coef=fit_poly(ns,ys,2); pred=sum(coef[i]*Fraction(1<<6)**i for i in range(3)); act=ksumset(6,k)
        if pred==act and all(c.denominator<=2 for c in coef):
            test_conjecture(f"K{k}",f"|{k}·μ_n| = {polystr(coef)}",
                lambda m,cc=coef:(lambda n:sum(cc[i]*Fraction(n)**i for i in range(3)))(1<<m),
                lambda m,kk=k:ksumset(m,kk),[2,3,4,5,6],"NOVEL-sumset")
        else:
            print(f"|{k}μ_n| fit non-poly or unverified: data {list(zip(ns,ys))} pred64 {pred} act {act}")
    except Exception as e:
        print(f"K{k} err {e}")

# --- Family 3: restricted sumset |{a+b : a,b in μ_n, a != b}| ---
def restr_sumset(m):
    n=1<<m; G,p=Gp(n,3)
    return len({(a+b)%p for a in G for b in G if a!=b})
pts=[2,3,4,5]; ns=[1<<m for m in pts]; ys=[restr_sumset(m) for m in pts]
coef=fit_poly(ns,ys,2); pred=sum(coef[i]*Fraction(1<<6)**i for i in range(3)); act=restr_sumset(6)
if pred==act:
    test_conjecture("R1",f"|{{a+b: a≠b in μ_n}}| = {polystr(coef)}",
        lambda m,cc=coef:(lambda n:sum(cc[i]*Fraction(n)**i for i in range(3)))(1<<m),
        restr_sumset,[2,3,4,5,6],"NOVEL")
else:
    print(f"R1 unverified: {list(zip(ns,ys))} pred64 {pred} act {act}")

# --- Family 4: multiplicative-additive — #{(a,b) in μ_n^2 : a*b + 1 in μ_n} ---
def muladd(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for a in G for b in G if (a*b+1)%p in S)
pts=[2,3,4,5]; ns=[1<<m for m in pts]; ys=[muladd(m) for m in pts]
print("muladd data:", list(zip(ns,ys)))
# conjecture: = n * (#{c in μ_n: c+1 in μ_n}) since a*b ranges over μ_n n-fold; test
def shifted(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for c in G if (c+1)%p in S)
test_conjecture("M1","#{(a,b)∈μ_n²: ab+1∈μ_n} = n · #{c∈μ_n: c+1∈μ_n}",
    lambda m:(1<<m)*shifted(m), muladd, [2,3,4,5],"NOVEL-mul-add")
# and #{c: c+1 in μ_n} closed form
pts=[1,2,3,4,5]; ns=[1<<m for m in pts]; ys=[shifted(m) for m in pts]
print("shifted (#{c:c+1∈μ_n}) data:", list(zip(ns,ys)))

print("\n==== BATCH 4 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")

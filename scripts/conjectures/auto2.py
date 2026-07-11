#!/usr/bin/env python3
"""Auto-generator 2: large sweep of lambda-incidences and set sizes; filters trivial
(group-closure / always-in-mu) survivors. Emits genuine novel survivors in bulk."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import big_prime_pow, mu
from fractions import Fraction
from collections import Counter

def Gp(n,power): p=big_prime_pow(n,power); return mu(p,n),p
def fit_poly(xs,ys,deg):
    A=[[Fraction(x)**j for j in range(deg+1)] for x in xs[:deg+1]]; b=[Fraction(y) for y in ys[:deg+1]]
    M=[A[i][:]+[b[i]] for i in range(deg+1)]; nn=deg+1
    for c in range(nn):
        piv=next((r for r in range(c,nn) if M[r][c]!=0),None)
        if piv is None: return None
        M[c],M[piv]=M[piv],M[c]; inv=Fraction(1)/M[c][c]; M[c]=[v*inv for v in M[c]]
        for r in range(nn):
            if r!=c and M[r][c]!=0: f=M[r][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(nn+1)]
    return [M[i][nn] for i in range(nn)]
def polystr(coef):
    t=[f"({coef[i]})n^{i}" if i>0 else f"({coef[i]})" for i in range(len(coef)-1,-1,-1) if coef[i]!=0]
    return " + ".join(t) or "0"
SURV=[]
def autofit(name, qfn, ms, maxdeg=3, trivial_check=None):
    try: ns=[1<<m for m in ms]; ys=[qfn(m) for m in ms]
    except Exception: return
    for deg in range(0, min(maxdeg,len(ms)-2)+1):
        coef=fit_poly(ns[:deg+1],ys[:deg+1],deg)
        if coef is None: continue
        if all(sum(coef[i]*Fraction(ns[t])**i for i in range(deg+1))==ys[t] for t in range(len(ns))):
            if len(ns)>=deg+3:
                tag = " [TRIVIAL]" if (trivial_check and trivial_check()) else ""
                SURV.append((name, polystr(coef), tag))
                print(f"[SURVIVE] {name} = {polystr(coef)}{tag}")
                return

ms=[2,3,4,5,6]
# lambda-incidence: #{(a,b)∈μ_n²: a+λb ∈ μ_n} for many λ
def inc(lam):
    def q(m):
        n=1<<m; G,p=Gp(n,3); S=set(G)
        return sum(1 for a in G for b in G if (a+lam*b)%p in S)
    return q
print("=== a+λb ∈ μ_n incidence family ===")
for lam in range(1,13):
    autofit(f"#{{a+{lam}b ∈ μ_n}}", inc(lam), ms, 2)
for lam in range(1,8):
    autofit(f"#{{a−{lam}b ∈ μ_n}}", inc(-lam), ms, 2)

# set size |{a+λb}| for many λ (genuine when not group)
def setsz(lam):
    def q(m):
        n=1<<m; G,p=Gp(n,3)
        return len({(a+lam*b)%p for a in G for b in G})
    return q
print("=== |{a+λb}| set-size family ===")
for lam in [2,3,4,5,6,7]:
    autofit(f"|{{a+{lam}b}}|", setsz(lam), ms, 2)

# pure power-incidence: #{(a,b): a^i + b^i ∈ μ_n} for i=1..5
def powinc(i):
    def q(m):
        n=1<<m; G,p=Gp(n,3); S=set(G)
        return sum(1 for a in G for b in G if (pow(a,i,p)+pow(b,i,p))%p in S)
    return q
print("=== a^i + b^i ∈ μ_n family ===")
for i in [1,2,3,4,5]:
    autofit(f"#{{a^{i}+b^{i} ∈ μ_n}}", powinc(i), [3,4,5,6], 2)

# 3-term: #{(a,b,c)∈μ_n³: a+b+λc = 0} for λ=2,3,..
def tri0(lam):
    def q(m):
        n=1<<m; G,p=Gp(n,4); c2=Counter()
        for a in G:
            for b in G: c2[(a+b)%p]+=1
        return sum(c2[(-lam*c)%p] for c in G)
    return q
print("=== a+b+λc=0 family ===")
for lam in [1,2,3,4]:
    autofit(f"#{{a+b+{lam}c=0}}", tri0(lam), [2,3,4,5], 2)

genuine=[s for s in SURV if not s[2]]
print(f"\n==== AUTO2: {len(SURV)} survivors ({len(genuine)} genuine, {len(SURV)-len(genuine)} trivial) ====")

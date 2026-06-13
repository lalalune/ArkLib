#!/usr/bin/env python3
"""Auto-generator: sweep many computable quantities on mu_n, fit-and-verify a closed form
(polynomial / constant / zero) on independent points, emit survivors. Scalable conjecture mining."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import big_prime_pow, mu
from fractions import Fraction
from collections import Counter
import itertools

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
    t=[]
    for i in range(len(coef)-1,-1,-1):
        if coef[i]!=0: t.append(f"({coef[i]})n^{i}" if i>0 else f"({coef[i]})")
    return " + ".join(t) or "0"

SURV=[]; DEAD=[]
def autofit(name, qfn, ms, maxdeg=4):
    """qfn(m)->int. Fit lowest-degree poly that matches all but verify on the LAST point held out."""
    try:
        ns=[1<<m for m in ms]; ys=[qfn(m) for m in ms]
    except Exception as e:
        return
    for deg in range(0, min(maxdeg, len(ms)-2)+1):
        coef=fit_poly(ns[:deg+1],ys[:deg+1],deg)
        if coef is None: continue
        # check ALL points (including held-out tail)
        good=all(sum(coef[i]*Fraction(ns[t])**i for i in range(deg+1))==ys[t] for t in range(len(ns)))
        if good:
            # require >= 2 verification points beyond the fit
            if len(ns) >= deg+3:
                SURV.append((name, polystr(coef), list(zip(ns,ys))))
                print(f"[SURVIVE] {name}: = {polystr(coef)}   data {list(zip(ns,ys))}")
                return
    DEAD.append((name, list(zip(ns,ys))))

# ---- quantity templates: #{(a,b)∈μ_n²: form(a,b) ∈ μ_n} ----
def make_in_mu(form):
    def q(m):
        n=1<<m; G,p=Gp(n,3); S=set(G)
        return sum(1 for a in G for b in G if form(a,b,p) in S)
    return q
forms = {
 "a+2b": lambda a,b,p:(a+2*b)%p,
 "2a+b": lambda a,b,p:(2*a+b)%p,
 "a+3b": lambda a,b,p:(a+3*b)%p,
 "3a-b": lambda a,b,p:(3*a-b)%p,
 "a-2b": lambda a,b,p:(a-2*b)%p,
 "a*b+a": lambda a,b,p:(a*b+a)%p,
 "a^2-b^2":lambda a,b,p:(a*a-b*b)%p,
 "a^2*b": lambda a,b,p:(a*a*b)%p,
 "a^2+ab":lambda a,b,p:(a*a+a*b)%p,
}
ms=[2,3,4,5,6]
for nm,f in forms.items():
    autofit(f"in_mu[{nm}]", make_in_mu(f), ms, maxdeg=2)

# ---- |{form(a,b): a,b∈μ_n}| set sizes ----
def make_setsize(form):
    def q(m):
        n=1<<m; G,p=Gp(n,3)
        return len({form(a,b,p) for a in G for b in G})
    return q
setforms={
 "a+2b": lambda a,b,p:(a+2*b)%p,
 "a-2b": lambda a,b,p:(a-2*b)%p,
 "2a+3b":lambda a,b,p:(2*a+3*b)%p,
 "a^2+b^2":lambda a,b,p:(a*a+b*b)%p,
 "ab":lambda a,b,p:(a*b)%p,
 "a+b^2":lambda a,b,p:(a+b*b)%p,
}
for nm,f in setforms.items():
    autofit(f"|{{{nm}}}|", make_setsize(f), ms, maxdeg=2)

# ---- 3-variable additive incidences #{(a,b,c): a+b+c ∈ specific} ----
def triple_in(form):
    def q(m):
        n=1<<m; G,p=Gp(n,4); S=set(G)
        c2=Counter()
        for a in G:
            for b in G: c2[(a+b)%p]+=1
        return sum(c2[(form(c,p)) % p]*1 for c in G for _ in [0]) if False else \
               sum(c2[(form(c,p))%p] for c in G)
    return q
# #{(a,b,c)∈μ_n³: a+b+c=0} done (Z_3=0). try a+b+c = 2c-equiv etc handled. skip.

print(f"\n==== AUTO SUMMARY: {len(SURV)} survivors, {len(DEAD)} non-poly/dead ====")
for nm,d in DEAD: print(f"  [no-closed-form] {nm}: {d}")

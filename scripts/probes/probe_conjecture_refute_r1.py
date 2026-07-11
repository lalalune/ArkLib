#!/usr/bin/env python3
"""
GENERATE-AND-REFUTE, Round 1 (#389): measure worst-case RS-over-mu_n list past Johnson,
and stress-test a battery of candidate closed-form bounds. A bound that is ever EXCEEDED is
REFUTED; one never exceeded across the sweep is a surviving CANDIDATE (NOT proven).

Setup: mu_n ⊂ F_p (n|p-1), RS deg<k. For received f: mu_n->F_p, list(f,a) = #{deg<k poly p :
agreement(eval p, f) >= a}. We hill-climb f to MAXIMIZE list, at radii a past Johnson sqrt(nk).
Large-field regime (p >> n) = the prize-relevant regime.

Candidate bounds tested (invent freely; refute by counterexample):
  J     = floor(n^2/(a^2-n*(k-1)))         Johnson (vacuous/neg past Johnson -> expect REFUTED/NA)
  C_2k  = 2*k-1                              "double-Johnson": list ~ 2k regardless of a
  C_lin = n-a+1                              linear in #errors
  C_kerr= (k)*(n-a)+1                        k * #errors
  C_tow = (n-a+1)*ceil(log2(n))             tower-scaled
  C_jvar= ceil( (k*(n-a+1)) / max(1,a-k+1) ) a Johnson-style ratio, k*errors/(margin)
"""
import math, random
from itertools import product

def evals(co, D, p): return tuple((lambda x:(lambda:0)())() for _ in ())  # placeholder unused

def codeword(co, D, p):
    out=[]
    for x in D:
        v=0;xp=1
        for c in co: v=(v+c*xp)%p; xp=(xp*x)%p
        out.append(v)
    return tuple(out)

def all_cws(D,k,p): return [codeword(co,D,p) for co in product(range(p),repeat=k)]

def listsize(f,C,a):
    n=len(f);cnt=0
    for c in C:
        ag=0
        for i in range(n):
            if c[i]==f[i]: ag+=1
        if ag>=a: cnt+=1
    return cnt

def maxlist(D,k,p,a,restarts,climb,rng):
    C=all_cws(D,k,p);n=len(D);best=0;bestf=None
    for _ in range(restarts):
        f=[rng.randrange(p) for _ in range(n)];cur=listsize(f,C,a)
        for _ in range(climb):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=listsize(f,C,a)
            if nl>=cur: cur=nl
            else: f[i]=old
        if cur>best: best=cur;bestf=f[:]
    return best,bestf

def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None: return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None

def candidates(n,k,a):
    J = (n*n)//(a*a-n*(k-1)) if a*a-n*(k-1)>0 else None
    return {
        "J(Johnson)": J,
        "C_2k=2k-1": 2*k-1,
        "C_lin=n-a+1": n-a+1,
        "C_kerr=k(n-a)+1": k*(n-a)+1,
        "C_tow=(n-a+1)ceil(log2 n)": (n-a+1)*math.ceil(math.log2(n)),
        "C_jvar=ceil(k(n-a+1)/(a-k+1))": math.ceil(k*(n-a+1)/max(1,a-k+1)),
    }

def run(p,n,k,restarts,climb,seed=0):
    rng=random.Random(seed);D=mun(p,n)
    if D is None: print(f"(p={p} n={n}: no mu_n)",flush=True);return {}
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} (large-field p/n^2={p/n**2:.1f}) Johnson agr sqrt(nk)={J:.2f}",flush=True)
    res={}
    for a in range(k+1, math.ceil(J)+1):  # a from k+1 (nonempty list) up to Johnson
        ml,_=maxlist(D,k,p,a,restarts,climb,random.Random(seed))
        cs=candidates(n,k,a)
        verdicts=[]
        for name,b in cs.items():
            if b is None: verdicts.append(f"{name}=NA")
            else: verdicts.append(f"{name}={b}{'!!REFUTED' if ml>b else ''}")
        past = "PAST" if a<J else "  -"
        print(f"  a={a:>2} {past} maxlist={ml:>3} | "+" ".join(verdicts),flush=True)
        res[a]=ml
    return res

if __name__=="__main__":
    run(p=97, n=8, k=2, restarts=18, climb=22)
    run(p=89, n=8, k=3, restarts=16, climb=20)
    run(p=151,n=10,k=2, restarts=16, climb=22)
    run(p=181,n=10,k=3, restarts=14, climb=20)

#!/usr/bin/env python3
"""CORRECTED census probe: worst alignable-SET / #GAMMA count vs the TRUE budget.

CORRECTION to my earlier probe: the weld's budget is NOT n. It is
   K < 2^r * C(2^{mu-1}, r)     (from hεstar < (2^r C(2^{mu-1},r))/p, K/p <= eps*).
This is exactly the KKH26 fibre supply count (the lower-bound construction).

So CensusDomination@budget asks: is  max_lines #alignable-sets(a0)  <=  2^r*C(2^{mu-1},r) ?
And the SHARP question: is  max_lines #distinct-gamma(a0)  <=  that budget?  (the real MCA need)

If #alignable-SETS <= budget : weld fires, delta* pinned (prize closed at this scale, modulo
asymptotic). If it EXCEEDS the budget over some line : that line is a witness that the deployed
CensusDomination Prop is FALSE at the budget => the weld cannot fire => the census normal form
does NOT reduce the prize to a free combinatorial count; the gap = BGK content.
"""
import itertools, math, sys
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def find_g(p,n):
    for h in range(2,4000):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in prime_factors(n)): return x
    raise ValueError
def census(u0,u1,xs,p,k,a):
    n=len(xs); e0={}; e1={}
    for T in itertools.combinations(range(n),k+1):
        t0=t1=0
        for i in T:
            den=1
            for j in T:
                if i!=j: den=den*((xs[i]-xs[j])%p)%p
            inv=pow(den,-1,p); t0=(t0+u0[i]*inv)%p; t1=(t1+u1[i]*inv)%p
        e0[T]=t0; e1[T]=t1
    def ratio(T):
        a_,b_=e0[T],e1[T]
        if b_!=0: return (-a_)*pow(b_,-1,p)%p
        return None if a_==0 else 'X'
    sets=0; gam=set()
    for S in itertools.combinations(range(n),a):
        r=None; ok=True; nd=False
        for T in itertools.combinations(S,k+1):
            rt=ratio(T)
            if rt is None: continue
            if rt=='X': ok=False; break
            nd=True
            if r is None: r=rt
            elif r!=rt: ok=False; break
        if ok and nd: sets+=1; gam.add(r)
    return sets,len(gam)

def run(n,mu,m,r,p):
    k=(r-2)*m+1; a0=r*m+1
    budget = 2**r * comb(2**(mu-1), r)
    g=find_g(p,n); xs=[pow(g,i,p) for i in range(n)]
    assert len(set(xs))==n
    beta=math.log(p)/math.log(n)
    cand=sorted(set([(j,j-1) for j in range(2,n)]+[(j,j-2) for j in range(3,n)]+[(n//2,n//2-1),(n//2+1,n//2-1)]))
    ws=(0,None); wg=(0,None)
    for (aa,bb) in cand:
        if aa>=n or bb<0 or aa==bb: continue
        u0=[pow(x,aa,p) for x in xs]; u1=[pow(x,bb,p) for x in xs]
        s,gm=census(u0,u1,xs,p,k,a0)
        if s>ws[0]: ws=(s,f"x^{aa},x^{bb}")
        if gm>wg[0]: wg=(gm,f"x^{aa},x^{bb}")
    print(f"n={n} mu={mu} m={m} r={r} k={k} a0={a0} p={p} beta={beta:.2f} | budget 2^r*C(2^(mu-1),r)={budget}")
    print(f"   worst #SETS={ws[0]} ({ws[1]}) {'<=' if ws[0]<=budget else '> !!'} budget {budget}")
    print(f"   worst #GAMMA={wg[0]} ({wg[1]}) {'<=' if wg[0]<=budget else '> !!'} budget {budget}")
    return (n,r,ws[0],wg[0],budget)

def main():
    # n=2^mu*m, m=1 => n=2^mu. prize p~n^4.
    configs=[
        # n, mu, m, r, p
        (8,3,1,2,4129), (8,3,1,3,4129),
        (16,4,1,3,65537),(16,4,1,4,65537),(16,4,1,5,65537),
    ]
    res=[]
    for c in configs:
        try: res.append(run(*c))
        except Exception as e: print(f"[skip {c}: {e}]")
    print("\n==== SUMMARY: worst count vs TRUE budget 2^r*C(2^(mu-1),r) ====")
    print(f"  {'n':>3} {'r':>2} | {'#SETS':>6} {'#GAMMA':>6} {'budget':>7} | sets / gamma verdict")
    for (n,r,s,gm,b) in res:
        print(f"  {n:>3} {r:>2} | {s:>6} {gm:>6} {b:>7} | sets:{'OK' if s<=b else 'EXCEEDS'} gamma:{'OK' if gm<=b else 'EXCEEDS'}")

if __name__=="__main__": sys.exit(main())

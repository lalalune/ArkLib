#!/usr/bin/env python3
"""
RULE-6 ADVERSARIAL RE-AUDIT of push 6feb11b53 (even moment inflated + exceeds sup prediction).
Two specific worries:
  W1. "exceeds sup prediction (M_thin/M_rand)^{2r}" could be random-control VARIANCE: the random MEDIAN
      moment uses a different random set than the random MEDIAN sup, so (E_rand)^{1/2r} and M_rand may come
      from different draws => the sup-prediction comparison is not apples-to-apples.
  W2. the inflation could shrink/vanish with MORE random draws (5 was thin).
FIX: per-draw self-consistent comparison. For EACH random draw, compute BOTH its M and its E_{2r} from the
SAME spectrum, form per-draw eff and per-draw (E_thin/E_draw) vs (M_thin/M_draw)^{2r}. Use 21 draws, report
the FULL distribution (min/median/max) of the random moment + whether thin EXCEEDS even the MOST concentrated
(max-moment) random draw. If thin > max random draw at deep r, the inflation is robust (not variance).
Also report whether (E_thin)^{1/2r} > (E_rand)^{1/2r} per-draw consistently.
"""
import cmath, math, random
from sympy import isprime
def prime_for(n,beta,seed=0,nf=False):
    base=int(round(n**beta)); t=max(2,base//n); tr=0
    while True:
        p=1+n*t
        if isprime(p) and (p-1)//n>1:
            if not nf or ((p-1)//n)%2==1 or (((p-1)//n)&((p-1)//n-1))!=0: return p
        t+=1; tr+=1
        if tr>500000: raise RuntimeError("no prime")
def primroot(p):
    order=p-1; x=order; fac=set(); d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    g=2
    while any(pow(g,order//q,p)==1 for q in fac): g+=1
    return g
def mu_n(p,n):
    m=(p-1)//n; h=pow(primroot(p),m,p); S=[]; cur=1
    for _ in range(n): S.append(cur); cur=cur*h%p
    assert len(set(S))==n and n!=p-1; return S
def absper(S,p):
    tp=2*math.pi/p; out=[]
    for b in range(1,p):
        s=0j
        for x in S: s+=cmath.exp(1j*tp*((b*x)%p))
        out.append(abs(s))
    return out
def analyze(n,beta,seed,nf=False,RMAX=6,ndraw=21):
    p=prize=prime_for(n,beta,seed,nf)
    At=absper(mu_n(p,n),p)
    M_thin=max(At)
    rnd=random.Random(seed*31+5)
    draws=[]
    for _ in range(ndraw):
        R=rnd.sample(range(1,p),n)
        sp=absper(R,p)
        draws.append(sp)
    print(f"\nn={n} beta={beta} p={p} m={(p-1)//n} {'[nf]' if nf else ''}  (ndraw={ndraw})")
    print(f"  M_thin={M_thin:.3f}; M_rand min/med/max = "
          f"{min(max(d) for d in draws):.3f}/{sorted(max(d) for d in draws)[ndraw//2]:.3f}/{max(max(d) for d in draws):.3f}")
    print("  r : E_thin/E_rand(med) | E_thin vs MAX-moment random draw | per-draw (E_th>E_dr) count | sup-EXCEED?")
    for r in range(1,RMAX+1):
        tr=2*r
        Et=sum(a**tr for a in At)
        Edraws=sorted(sum(a**tr for a in d) for d in draws)
        Emed=Edraws[ndraw//2]; Emax=Edraws[-1]
        gt_count=sum(1 for e in Edraws if Et>e)
        ratio_med=Et/Emed
        exceeds_max = Et>Emax
        # apples-to-apples sup prediction: use the SAME max-moment draw's own M
        # find the draw with the max moment, get its M
        idx_maxmom=max(range(ndraw), key=lambda i: sum(a**tr for a in draws[i]))
        M_that=max(draws[idx_maxmom])
        suppred=(M_thin/M_that)**tr
        ratio_that=Et/Emax
        exc = "YES" if ratio_that>suppred else "no"
        print(f"  {r}: {ratio_med:8.4f} | thin/{'>' if exceeds_max else '<='}max-draw ({ratio_that:.3f}) | {gt_count}/{ndraw} | "
              f"thin/maxdraw={ratio_that:.3f} vs sup-pred={suppred:.3f} -> EXCEEDS sup: {exc}")
def main():
    print("RULE-6 RE-AUDIT of 6feb11b53: per-draw self-consistent, 21 draws, apples-to-apples sup prediction.")
    for (n,beta,seed,nf) in [(16,4.0,1,False),(16,4.5,2,True)]:
        analyze(n,beta,seed,nf)
if __name__=="__main__": main()

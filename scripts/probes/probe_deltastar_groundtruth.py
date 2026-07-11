#!/usr/bin/env python3
"""
TOY-MODEL GROUND TRUTH of delta* (ABF26 Def 4.3, faithful).

mcaEvent(C,delta,u0,u1,gamma) = exists S, |S|>=(1-delta)n, exists w in C with
  w=u0+gamma*u1 on S, and NOT jointAgree(S) [u0|S and u1|S each interpolate deg<k].
epsMCA(C,delta) = max over stacks (u0,u1) of |{gamma: mcaEvent}|/|F|.
delta* = sup{delta: epsMCA <= eps*}.

For RS over F_p, deg<k, domain = k_dom distinct points. mcaEvent via w <=>
  |agree(w,line)|>=t AND not(consistent(u0,A_w) and consistent(u1,A_w)),
A_w=agree(w,line), t=ceil((1-delta)n). Reduces over thresholds t=n..1.
Compare the per-threshold max prob to candidate delta formulas + prize delta*=1/4.
"""
import itertools

def consistent(vals, S, pts, k, p):
    # does u|S interpolate to a deg<k poly? (Vandermonde rank / interpolate k pts, check rest)
    Sl=sorted(S)
    if len(Sl)<=k: return True
    # interpolate first k points, check the rest
    xs=[pts[i] for i in Sl]; ys=[vals[i] for i in Sl]
    # Lagrange over F_p on first k
    base=Sl[:k]
    def interp(x):
        tot=0
        for a in base:
            xa=pts[a]; num=1; den=1
            for b in base:
                if b==a: continue
                num=(num*((x-pts[b])%p))%p; den=(den*((xa-pts[b])%p))%p
            tot=(tot+vals[a]*num*pow(den,p-2,p))%p
        return tot
    return all(interp(pts[i])==vals[i] for i in Sl[k:])

def run(p,k,n):
    pts=list(range(1,n+1))           # n distinct nonzero eval points (need n<=p-1)
    assert n<=p
    # codewords: deg<k polys
    cws=[]
    for co in itertools.product(range(p),repeat=k):
        cws.append(tuple(sum(co[j]*pow(x,j,p) for j in range(k))%p for x in pts))
    # max prob per threshold t over all stacks
    best={t:0 for t in range(1,n+1)}
    beststack={t:None for t in range(1,n+1)}
    F=range(p)
    for u0 in itertools.product(F,repeat=n):
        for u1 in itertools.product(F,repeat=n):
            if all(v==0 for v in u1): continue
            # count, per threshold, #gamma with mcaEvent
            cnt={t:0 for t in range(1,n+1)}
            for g in F:
                line=tuple((u0[i]+g*u1[i])%p for i in range(n))
                # find, per threshold t, whether mcaEvent holds (exists w)
                hit={t:False for t in range(1,n+1)}
                for w in cws:
                    A=[i for i in range(n) if w[i]==line[i]]
                    a=len(A)
                    if a==0: continue
                    ja = consistent(u0,A,pts,k,p) and consistent(u1,A,pts,k,p)
                    if not ja:
                        for t in range(1,a+1): hit[t]=True
                for t in range(1,n+1):
                    if hit[t]: cnt[t]+=1
            for t in range(1,n+1):
                if cnt[t]>best[t]:
                    best[t]=cnt[t]; beststack[t]=(u0,u1)
    return pts,best

def run_cosets(p,k,n):
    """Same as run() but stacks range over coset reps (first k coords = 0): p^(n-k) each."""
    pts=list(range(1,n+1))
    cws=[]
    for co in itertools.product(range(p),repeat=k):
        cws.append(tuple(sum(co[j]*pow(x,j,p) for j in range(k))%p for x in pts))
    # coset reps: words that are 0 on coords 0..k-1, free on k..n-1
    def reps():
        for tail in itertools.product(range(p),repeat=n-k):
            yield tuple([0]*k)+tail
    best={t:0 for t in range(1,n+1)}; bs={t:None for t in range(1,n+1)}
    for u0 in reps():
        for u1 in reps():
            if all(v==0 for v in u1): continue
            cnt={t:0 for t in range(1,n+1)}
            for g in range(p):
                line=tuple((u0[i]+g*u1[i])%p for i in range(n))
                hit={t:False for t in range(1,n+1)}
                for w in cws:
                    A=[i for i in range(n) if w[i]==line[i]]
                    if not A: continue
                    if not (consistent(u0,A,pts,k,p) and consistent(u1,A,pts,k,p)):
                        for t in range(1,len(A)+1): hit[t]=True
                for t in range(1,n+1):
                    if hit[t]: cnt[t]+=1
            for t in range(1,n+1):
                if cnt[t]>best[t]: best[t]=cnt[t]; bs[t]=(u0,u1)
    return best,bs

if __name__=="__main__":
    import sys
    for (p,k,n) in [(5,2,4),(7,2,4),(7,3,5),(7,2,5)]:
        best,bs=run_cosets(p,k,n)
        rho=k/n
        print(f"\n=== RS[F{p}, k={k}, n={n}] rho={rho:.3f}  Johnson 1-sqrt(rho)={1-rho**0.5:.3f}  "
              f"halfJ={(1-rho**0.5)/2:.3f}  (1-rho)/3={(1-rho)/3:.3f}  cap 1-rho={1-rho:.3f} ===")
        print(f"  t(|S|>=t)  delta=1-t/n   maxProb=epsMCA(delta)  [worst |mcaBad|/{p}]")
        for t in range(n,0,-1):
            delta=1-t/n
            print(f"   t={t}      delta={delta:.3f}        {best[t]}/{p} = {best[t]/p:.3f}")

# BandExactness oracle-validation: in-band |mcaBad|(j)=j+1 confirmed on F5/F7 instances;
# spikes outside 3j<n-k+1. Production delta* lives in the census/spike band (list-decoding regime).

# S2 REFUTED: smooth-domain (mu_n) worst-case census = generic-domain census (n=4: both [1,4,4,4]
# at rho=.5). Coset/multiplicative structure does NOT ease the worst-case floor - adversary picks
# the worst stack regardless of domain. Prize smooth-domain restriction does not help the census wall.

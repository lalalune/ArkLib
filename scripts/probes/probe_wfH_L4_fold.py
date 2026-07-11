# wfH-L4 EXACT fold check: max_c |sum_{x in mu_n} e_p(c x^2)| == 2 * max_c |sum_{y in mu_{n/2}} e_p(c y)|
# = 2 * M(mu_{n/2})  -- because x->x^2 is 2-to-1 from mu_n onto mu_{n/2}.
# This is the load-bearing identity: a PURE QUADRATIC phase over mu_n IS a LINEAR Gauss period
# over the half-size 2-power subgroup mu_{n/2} (times 2). So U^3 returns the SAME wall, smaller n.
import numpy as np, math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def subgroup(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def maxlin(roots,p,w):
    best=-1.0;arg=None
    for c in range(1,p):
        ph=(c*roots)%p; v=abs(w[ph].sum())
        if v>best:best=v;arg=c
    return best,arg
def run(n,beta):
    target=n**beta; p=((target)//n)*n+1
    while p<target or not isprime(p): p+=n
    w=np.exp(2j*math.pi*np.arange(p)/p)
    rn=np.array(subgroup(p,n),dtype=np.int64)
    rh=np.array(subgroup(p,n//2),dtype=np.int64)
    sq=(rn*rn)%p
    # pure quadratic max over c (b=0)
    bestQ=-1.0;argQ=None
    for c in range(1,p):
        ph=(c*sq)%p; v=abs(w[ph].sum())
        if v>bestQ:bestQ=v;argQ=c
    Mhalf,argh=maxlin(rh,p,w)
    Mfull,_=maxlin(rn,p,w)
    # EXACT integer check that the squared-multiset is exactly 2 copies of mu_{n/2}
    from collections import Counter
    sqc=Counter(int(x) for x in sq); hh=set(int(x) for x in rh)
    exact_double = (set(sqc)==hh) and all(v==2 for v in sqc.values())
    return p,bestQ,argQ,Mhalf,argh,Mfull,exact_double, abs(bestQ-2*Mhalf)
if __name__=="__main__":
    print("# Q_pure(n)=max_c|sum_{mu_n} e(c x^2)|  vs  2*M(mu_{n/2}). exact_double = (mu_n^2 = 2.mu_{n/2}).")
    for n,beta in [(8,4),(16,3),(16,2),(32,2),(64,2)]:
        p,Q,argQ,Mh,argh,Mf,exd,diff=run(n,beta)
        print(f"n={n:3d} b={beta} p={p:6d} | Q_pure={Q:.5f}(c={argQ}) | 2*M(mu_{n//2})={2*Mh:.5f}(c={argh}) "
              f"| |Q-2Mhalf|={diff:.2e} | M(mu_n)={Mf:.4f} | Q/Mfull={Q/Mf:.3f} | exact_double={exd}",flush=True)

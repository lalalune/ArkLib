#!/usr/bin/env python3
"""
probe_407_even_census_dcsub.py  -- ADVERSARIAL re-audit (rule 6) of the even-census-profile finding.

The first probe found E_{2r}(thin) / E_{2r}(random) GROWS with r (1->8.85). CAVEAT to rule out:
the even energy moment sum_{b!=0}|eta_b|^{2r} is dominated by the LARGEST few |eta_b| (the sup M).
A larger thin moment could be ENTIRELY the known fact "thin M >= random M" (852e0fa27, ILO) re-seen,
NOT a genuinely new collective/per-depth signal. To separate:

1. Report M_thin vs M_rand (the sup) and (E_{2r})^{1/2r} -> M as r grows. If the ratio growth is just
   (M_thin/M_rand)^{2r}, it's the SUP fact re-expressed, not new.
2. DC-subtraction is irrelevant here: sum is over b!=0, so eta_0=|G|=n is EXCLUDED already. Good.
3. KEY new test: the SHAPE of the period distribution {|eta_b|}_{b!=0}, not just its max. Compare the
   full sorted spectrum thin vs random: is thin MORE top-heavy at EVERY quantile (collective), or only
   at the extreme tail (sup only)? Compute the ratio of the t-th largest |eta_b| thin/random for
   t = 1, 2, 4, 8, ... and the L^{2r} norm growth.
4. Verify (E_{2r})^{1/2r}/M -> 1 and whether thin's approach is slower/faster (tail spread).

VERDICT target: is the compounding E-ratio a NEW collective signal or the SUP fact in disguise?
"""
import cmath, math, random
from sympy import isprime

def prime_for(n, beta, seed=0, want_non_fermat=False):
    base = int(round(n**beta)); t = max(2, base//n); tried=0
    while True:
        p = 1+n*t
        if isprime(p) and (p-1)//n > 1:
            if not want_non_fermat or ((p-1)//n)%2==1 or (((p-1)//n)&((p-1)//n-1))!=0:
                return p
        t+=1; tried+=1
        if tried>500000: raise RuntimeError("no prime")

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
    assert len(set(S))==n and n!=p-1
    return S

def abs_periods(S,p):
    n=len(S); tp=2*math.pi/p; out=[0.0]*p
    for b in range(1,p):
        s=0j
        for x in S: s+=cmath.exp(1j*tp*((b*x)%p))
        out[b]=abs(s)
    return out[1:]  # b=1..p-1

def analyze(n,beta,seed,nf=False,R_MAX=6,n_rand=5):
    p=prime_for(n,beta,seed,nf)
    A=sorted(abs_periods(mu_n(p,n),p),reverse=True)
    rnd=random.Random(seed*131+7)
    rand_specs=[]
    for _ in range(n_rand):
        R=rnd.sample(range(1,p),n)
        rand_specs.append(sorted(abs_periods(R,p),reverse=True))
    # median random spectrum (per-rank median)
    L=len(A)
    Rmed=[sorted(rand_specs[k][i] for k in range(n_rand))[n_rand//2] for i in range(L)]
    M_thin=A[0]; M_rand=Rmed[0]
    print(f"\nn={n} beta={beta} p={p} m={(p-1)//n} {'[nf]' if nf else ''}")
    print(f"  SUP: M_thin={M_thin:.3f}  M_rand={M_rand:.3f}  ratio={M_thin/M_rand:.4f}  sqrt(n log(p/n))={math.sqrt(n*math.log(p/n)):.3f}")
    # quantile ratios: t-th largest thin/rand
    print("  rank-t |eta| thin/rand (collective shape):")
    ts=[1,2,4,8,16,32,64,128]
    qs=[]
    for t in ts:
        if t<=L:
            qr=A[t-1]/Rmed[t-1] if Rmed[t-1]>0 else float('inf')
            qs.append((t,A[t-1],Rmed[t-1],qr))
    for (t,at,rt,qr) in qs:
        print(f"     t={t:>4}: thin={at:8.3f} rand={rt:8.3f}  ratio={qr:.4f}")
    # E_{2r} ratio and (E)^{1/2r}, plus the "sup-only prediction" (M_thin/M_rand)^{2r}
    print("  r : E2r_thin/E2r_rand | (E_thin)^{1/2r} | (E_rand)^{1/2r} | sup-pred (Mt/Mr)^{2r}")
    base_ratio=M_thin/M_rand
    for r in range(1,R_MAX+1):
        tr=2*r
        Et=sum(a**tr for a in A); Er=sum(a**tr for a in Rmed)
        rat=Et/Er
        et=Et**(1/tr); er=Er**(1/tr)
        suppred=base_ratio**tr
        print(f"  {r}: {rat:10.4f} | {et:10.3f} | {er:10.3f} | {suppred:10.4f}   ({'SUP-EXPLAINED' if abs(rat-suppred)/suppred<0.25 else 'EXCEEDS sup pred' if rat>suppred else 'BELOW sup pred'})")

def main():
    print("ADVERSARIAL re-audit: is the even-moment thin>random growth a NEW collective signal or the SUP fact?")
    for (n,beta,seed,nf) in [(16,4.0,1,False),(16,4.5,2,True),(32,4.0,3,False)]:
        analyze(n,beta,seed,nf)

if __name__=="__main__":
    main()

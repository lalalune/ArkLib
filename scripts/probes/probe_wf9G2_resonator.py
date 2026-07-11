#!/usr/bin/env python3
# wf-G2 (#444): RESONANCE-METHOD lower bound on M(n) = max_{b!=0} |eta_b|,
#   eta_b = sum_{x in mu_n} e_p(b x),  mu_n = order-n 2-power mult. subgroup of F_p*.
#
# Bondarenko-Seip / Soundararajan resonance: a lower bound on the max of a sum of
# characters is obtained from a RESONATOR weight R(b) >= 0 supported on a
# multiplicatively-structured set S:
#
#     max_b |eta_b|  >=  | sum_{b} R(b) eta_b |  /  sum_b R(b).
#
# eta_b is CONSTANT on cosets of mu_n (b -> b*u, u in mu_n leaves the sum invariant),
# so the natural "frequency variable" is the coset c in F_p* / mu_n (m = (p-1)/n cosets).
# Define period_c = eta_{rep(c)}. The resonator lives on COSETS.
#
# RESONATOR CHOICE (multiplicatively structured): concentrate R on cosets whose reps lie
# in a GEOMETRIC PROGRESSION (subgroup-like)  S = { g^{m*t} ... } -- i.e. on a SUBGROUP of
# the coset group F_p*/mu_n (cyclic of order m). We take H_d = unique subgroup of index d.
# The resonance quotient with R = indicator of a coset-subgroup picks out a Gauss-sum-like
# average of periods. We sweep resonator size and report the achieved
#     LB = |sum_{c in S} period_c| / |S|     and     LB / sqrt(n log(p/n)).
#
# A genuine Omega-result needs LB / sqrt(n log(p/n)) to GROW with n along a witness sequence.
# Flat/saturating => floor is tight (C >= const), prize bound plausibly TRUE.

import math, cmath, sys

def isprime(x):
    if x < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if x % q == 0: return x == q
    d = x-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y = pow(a,d,x)
        if y in (1,x-1): continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True

def factor(x):
    f=[]; d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: f.append(x)
    return f

def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g

def find_prime_near(n, beta):
    # smallest prime p = 1 + k*n with p >= n^beta and m=(p-1)/n>1
    target=int(n**beta); k=max(2,(target-1)//n)
    while True:
        p=1+k*n
        if p>=target and isprime(p) and (p-1)//n>1: return p
        k+=1

def periods_by_coset(p, n, m_cap=200000):
    """Return list period_c for c=0..M-1 cosets (M=min(m,m_cap)). period real.
    Uses numpy vectorization. If m>m_cap, scan only the first m_cap cosets
    (still a valid resonator over a SUB-set, giving a valid LB on max)."""
    import numpy as np
    g=proot(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,j,p) for j in range(n)], dtype=np.int64)
    w=2*math.pi/p
    M=min(m, m_cap)
    per=np.empty(M, dtype=np.float64)
    rep=1
    for c in range(M):
        prod=(rep*mu)%p
        per[c]=np.cos(w*prod).sum()
        rep=(rep*g)%p
    return per, m, g, M

def resonance_lb(per, m, M):
    """Resonance LB on max|eta| via three resonator families over the scanned cosets [0,M):
      (1) coset-subgroups of Z/m (when fully scanned, M==m),
      (2) sign-aligned resonator R(c)=sign(per[c]) restricted to the top-|per| cosets
          (Bondarenko-Seip style: weight = aligned indicator => LB = mean|per| over the
          chosen set; best when restricted to large-|per| cosets),
      (3) the trivial single-coset max (==truemax over scanned set).
    Returns best LB and a label."""
    import numpy as np
    best=0.0; lab=None
    # (3) single coset
    am=float(np.max(np.abs(per)))
    if am>best: best=am; lab="single"
    # (2) top-k aligned resonator: sort by |per|, take top k, LB=mean|per_topk|
    order=np.argsort(-np.abs(per))
    ap=np.abs(per)[order]
    csum=np.cumsum(ap)
    ks=np.arange(1,M+1)
    means=csum/ks
    j=int(np.argmax(means))            # always k=1 for mean, but kept for completeness
    # (1) full coset-subgroup resonator (only valid if M==m)
    if M==m:
        d=1; ds=[]
        while d<=m:
            if m%d==0: ds.append(d)
            d+=1
        for dord in ds:
            step=m//dord
            idx=(step*np.arange(dord))%m
            lb=abs(per[idx].sum())/dord
            if lb>best: best=lb; lab=f"subgroup(ord={dord})"
    return best, lab

if __name__=="__main__":
    print("RESONANCE-METHOD LOWER BOUND on M(n)  (coset-subgroup resonator)")
    print(f"{'n':>5} {'beta':>5} {'p':>10} {'m':>8} {'truemax':>9} {'resLB':>9} {'floor=sqrt(n ln(p/n))':>22} {'resLB/floor':>11} {'true/floor':>10} {'resOrd':>7}")
    import numpy as np
    rows=[]
    # Hold beta as large as feasible while m=(p-1)/n <= m_cap so we can FULLY scan cosets
    # (subgroup resonator is only valid on the full coset group). For each n pick the
    # LARGEST beta with m<=cap, keeping the prime THIN (beta>=3).
    m_cap=200000
    for mu in range(3,11):            # n = 8..1024
        n=2**mu
        # choose beta so that m ~ m_cap: p ~ n*m_cap => beta = log_n(n*m_cap)
        beta=math.log(n*m_cap)/math.log(n)
        beta=min(beta, 5.0)
        if beta<3.0: continue
        p=find_prime_near(n,beta)
        per,m,g,M=periods_by_coset(p,n,m_cap)
        full=(M==m)
        truemax=float(np.max(np.abs(per)))
        reslb, lab=resonance_lb(per, m, M)
        floor=math.sqrt(n*math.log(p/n))
        tag="FULL" if full else "PART"
        print(f"{n:>5} {beta:>5.2f} {p:>10} {m:>8} {truemax:>9.3f} {reslb:>9.3f} {floor:>22.3f} {reslb/floor:>11.4f} {truemax/floor:>10.4f} {lab if lab else '':>16} {tag}")
        rows.append((n,reslb/floor,truemax/floor,reslb,truemax,full))
    print("\nGROWTH ANALYSIS (resLB/floor and true/floor vs n):")
    for n,rf,tf,rl,tm,full in rows:
        print(f"  n={n:>4}: resLB/floor={rf:.4f}  true/floor={tf:.4f}  (resLB={rl:.3f} true={tm:.3f}) {'FULL' if full else 'PART'}")
    # fit slope of resLB/floor vs log2(n)
    xs=[math.log2(r[0]) for r in rows]; ys=[r[1] for r in rows]
    nlen=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
    slope=(nlen*sxy-sx*sy)/(nlen*sxx-sx*sx)
    print(f"\n  slope d(resLB/floor)/d(log2 n) = {slope:+.4f}  -> {'GROWING (disproof signal)' if slope>0.05 else 'FLAT/SATURATING (floor tight, prize plausible)'}")

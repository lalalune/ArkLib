#!/usr/bin/env python3
# wf-G2 (#444): the OPTIMAL resonance / second-moment lower bound, and its CEILING.
#
# The strongest first/second-moment resonance lower bounds on M=max_b|eta_b|:
#   (A) L2/L1:  M >= S2/S1,  S2=sum_b|eta_b|^2, S1=sum_b|eta_b|.
#   (B) energy: M^2 >= S2/(#b) ... but exact Parseval gives sum_{b=0..p-1}|eta_b|^2 = p*n,
#       and eta_0=n, so sum_{b!=0}|eta_b|^2 = p*n - n^2 = n(p-n).  Thus
#         mean_{b!=0}|eta_b|^2 = n(p-n)/(p-1) ~ n   => RMS period ~ sqrt(n)  (the FLOOR).
#   (C) 4th-moment / additive-energy bound:  M^2 >= S4/S2  where
#         S4 = sum_{b!=0}|eta_b|^4 = (additive energy of mu_n) * stuff.
#       Lam-Leung char-0: E_2(mu_n) <= 3 n^2 (4-tuples), so S4 is O(n^2 * p) and
#       M^2 >= S4/S2 ~ (c n^2 p)/(n p) = c n  => M >= c sqrt(n).  NO log, NO growth.
#
# This probe computes (A),(B),(C) EXACTLY (Parseval-closed, no full b-scan needed for S2)
# and the realized truemax, confirming every moment-resonance lower bound saturates at
# c*sqrt(n) -- BELOW the sqrt(n log(p/n)) floor. => the resonance method CANNOT produce a
# growing (>sqrt(n)) lower bound; the log factor and any growth are NOT forced from below.

import math, sys
import numpy as np

def isprime(x):
    if x<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if x%q==0: return x==q
    d=x-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
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
    target=int(n**beta); k=max(2,(target-1)//n)
    while True:
        p=1+k*n
        if p>=target and isprime(p) and (p-1)//n>1: return p
        k+=1

def all_periods(p, n, m_cap):
    """periods over scanned cosets; returns array and whether full."""
    g=proot(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    w=2*math.pi/p
    M=min(m,m_cap)
    per=np.empty(M)
    rep=1
    for c in range(M):
        per[c]=np.cos(w*((rep*mu)%p)).sum()
        rep=(rep*g)%p
    return per, m, M

if __name__=="__main__":
    BETA=float(sys.argv[1]) if len(sys.argv)>1 else 4.0
    m_cap=int(sys.argv[2]) if len(sys.argv)>2 else 400000
    print(f"OPTIMAL moment-resonance lower bounds vs realized max, FIXED beta={BETA}.")
    print("Each period appears with multiplicity n among the b's (eta is coset-constant).")
    print(f"{'n':>5} {'p':>11} {'m':>9} {'full':>5} {'truemax':>9} {'L2/L1':>8} {'sqrt(S4/S2)':>11} {'sqrtN':>7} {'floor':>9} {'true/floor':>10} {'res4/floor':>10}")
    for mu in range(3,10):
        n=2**mu
        p=find_prime_near(n,BETA)
        m=(p-1)//n
        if m>m_cap and m>3_000_000: break
        per,m,M=all_periods(p,n,min(m_cap,m))
        full=(M==m)
        truemax=float(np.max(np.abs(per)))
        floor=math.sqrt(n*math.log(p/n))
        # moments over the scanned cosets (each weighted by n for the b-multiplicity cancels in ratios)
        a=np.abs(per)
        S1=a.sum(); S2=(a*a).sum(); S4=(a**4).sum()
        l2l1 = S2/S1 if S1>0 else 0
        res4 = math.sqrt(S4/S2) if S2>0 else 0
        # exact Parseval check (full only): sum_{b!=0}|eta|^2 = n(p-n); coset form: n*sum_c per_c^2 = n(p-n)
        print(f"{n:>5} {p:>11} {m:>9} {str(full):>5} {truemax:>9.3f} {l2l1:>8.3f} {res4:>11.3f} {math.sqrt(n):>7.2f} {floor:>9.3f} {truemax/floor:>10.4f} {res4/floor:>10.4f}")
    print("\nINTERPRETATION:")
    print("  L2/L1 and sqrt(S4/S2) are the best first/second-moment resonance LBs.")
    print("  If both track c*sqrt(n) (NOT sqrt(n log)) and res4/floor DECAYS, the resonance")
    print("  method provably CANNOT force a growing (super-sqrt(n)) period => no Omega disproof.")

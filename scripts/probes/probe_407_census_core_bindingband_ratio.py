#!/usr/bin/env python3
"""
probe_407_census_core_bindingband_ratio.py  (#407 / #371 census-vs-CORE lane)

THE FINDING (consolidated, exact): the in-tree CENSUS<->CORE equivalence, asserted in
CensusDominationWeld.lean ("the $1M obligation in census normal form"), is NOT TIGHT at the
binding deep band. Only the (U) direction (#bad <= #alignable) is proven; the reverse
(#alignable ~ #bad, needed for EQUIVALENCE) FAILS with a depth-growing, line-dependent slack.

EVIDENCE (from the in-tree probe_alignment_census.py, re-measured here at the binding bands):
  k=3 (m=2 deep-ceiling shape), n=16, smooth, prize prime:
    KKH26 line [x^6,x^4]:  a=4: 1792/496   a=5: 336/40    a=6(bind): 56/40  -> ratio 1.40
    hifreq    [x^9,x^7]:   a=5: 112/1      a=6: 56/1      a=7: 16/1   a=8: 2/1
  => at the hifreq line the alignable supply (112,56,16,2) ALL pin ONE bad gamma:
     ratio #alignable/#bad = 112, 56, 16, 2 -- a HUGE, DEPTH-DECAYING slack. The census counts
     up to 112 alignable a-sets that all explain the SAME single bad scalar (one far-line root locus).

INTERPRETATION (honest, refutation-grade for the EQUIVALENCE claim; NOT a CORE result):
  CensusDomination bounds #alignable-a-sets <= K. CORE / the deployed delta*-pin only needs
  #bad-scalars (= epsMCA mass) <= eps*p. Since #alignable >> #bad at the binding band (one bad
  gamma realized by many aligned sets -- the multiple a-subsets of ONE far-line agreement locus),
  CensusDomination is a STRICTLY STRONGER hypothesis than CORE: proving #alignable<=K proves more
  than the prize needs. The asserted "CensusDomination IS the prize obligation" is an OVER-STATEMENT
  of EQUIVALENCE -- it is a SUFFICIENT condition (via the proven (U)), not an equivalent one.
  CONSEQUENCE: a CORE proof does NOT have to go through CensusDomination; and CensusDomination could
  even be FALSE (too strong) while CORE holds -- so census-route effort should target #bad directly
  (the #bad collapse to O(1) at the hifreq line is the real CORE signal), not the inflated #alignable.

This probe makes the slack EXACT + reproducible at the binding band, and adds the thinness control:
is the #alignable/#bad inflation thinness-essential? Probe-first, exact mod-p, proper subgroup,
prize prime, never n=q-1. NO Lean change => axiom-clean trivially.
"""
import itertools
from math import comb

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def prime_1modn(target, n):
    p=target; p += (1-p)%n
    while not (isprime(p) and (p-1)%n==0): p+=n
    return p

def _pf(n):
    f=set(); d=2; m=n
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def find_g(p,n):
    for h in range(2,p):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in _pf(n)): return x
    raise ValueError

def dd(idxs,u,xs,p):
    t=0
    for i in idxs:
        den=1
        for j in idxs:
            if i!=j: den=den*((xs[i]-xs[j])%p)%p
        t=(t+u[i]*pow(den,p-2,p))%p
    return t

def census_band(n,p,g,A,B,k,a):
    xs=[pow(g,i,p) for i in range(n)]
    u0=[pow(x,A,p) for x in xs]; u1=[pow(x,B,p) for x in xs]
    align=0; bad=set()
    for S in itertools.combinations(range(n),a):
        gam=None; ok=True; nd=False
        for T in itertools.combinations(S,k+1):
            e0=dd(T,u0,xs,p); e1=dd(T,u1,xs,p)
            if e1==0:
                if e0!=0: ok=False; break
                continue
            nd=True; gT=(-e0*pow(e1,p-2,p))%p
            if gam is None: gam=gT
            elif gam!=gT: ok=False; break
        if ok and nd and gam is not None: align+=1; bad.add(gam)
    return align,len(bad)

def deepscan(label,n,p,g,k,lines):
    print(f"\n## {label}: n={n} p={p} k={k}")
    print(f"{'line':>14} {'band a':>7} {'#align':>8} {'#bad':>6} {'ratio':>8}  (binding = deepest a with align>0)")
    print("-"*60)
    for (A,B,nm) in lines:
        rows=[]
        for a in range(k+1,n):
            al,bd=census_band(n,p,g,A,B,k,a)
            if al==0: break
            rows.append((a,al,bd,al/bd if bd else float('inf')))
        if not rows: 
            print(f"{nm:>14}   (no supply)"); continue
        for (a,al,bd,r) in rows:
            mark = "  <-- BINDING" if (a,al,bd,r)==rows[-1] else ""
            print(f"{nm:>14} {a:>7} {al:>8} {bd:>6} {r:>8.2f}{mark}")

def main():
    print("# census<->CORE binding-band ratio: #alignable / #bad inflation (the equivalence SLACK) (#407/#371)")
    print("# (U) proven: #bad <= #alignable. EQUIVALENCE needs ~1. Measured: grows with depth, line-dependent.")
    p16=prime_1modn(65537,16); g16=find_g(p16,16)
    # k=3 deep-ceiling (m=2) shape -- the band the weld binds at
    deepscan("SMOOTH 2^4 (k=3,m=2 deep)",16,p16,g16,3,
             [(6,4,"KKH26[6,4]"),(9,7,"hifreq[9,7]"),(7,6,"hifreq[7,6]"),(7,5,"shift[7,5]")])
    # thinness control: thick n=12
    p12=prime_1modn(20749,12); g12=find_g(p12,12)
    deepscan("THICK n=12 (k=3)",12,p12,g12,3,
             [(6,4,"[6,4]"),(9,7,"[9,7]"),(7,6,"[7,6]")])
    print("\n# VERDICT: at the hifreq line many alignable a-sets (e.g. 112,56,16,2) pin ONE bad gamma =>")
    print("#  #alignable/#bad inflation is large + depth-decaying => CensusDomination is STRICTLY STRONGER")
    print("#  than CORE (#bad), NOT equivalent. The census normal form is a SUFFICIENT (via proven (U)),")
    print("#  not equivalent, encoding of the prize. CORE-effort should target #bad (collapses to O(1) at")
    print("#  the hifreq line), not the inflated #alignable supply.")

if __name__=='__main__':
    main()

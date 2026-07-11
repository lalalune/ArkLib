#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the BOTTOM-LEVEL cancellation budget at the worst frequency.

Context. _DoorIVCoherenceTowerCollapse (1acd54023) proved: at the worst b*, the dyadic
coherence tower COLLAPSES at the top (every upper level pinned ρ=1) and ALL coherence slack
lives at the BOTTOM level(s).  So the entire √-cancellation, if any, must come from the
bottom level: the μ_1-pairs  P_y = e_p(b·y) + e_p(b·(-y))  (the index-2 split of μ_2-cosets
into ±, since μ_n is neg-closed in the prize regime).

This probe asks the NEXT, finite, computable question the collapse result raises:
HOW MANY bottom pairs cancel, and HOW MUCH?  Define the bottom-level cancellation profile at
the worst b*:
   pairs P_y = e_p(b y) + e_p(-b y),  y ranging over a transversal of μ_n / {±1}  (n/2 pairs).
   |P_y| = 2|cos(2π b y / p)|  (real, since the pair is conjugate -> +/-2cos).
The half-mass at the bottom is  Σ_y |P_y|  =  Σ_y 2|cos(2π b y/p)|.  The PRIZE-relevant
question: is the worst-b a frequency for which the cosines are SYSTEMATICALLY large (few small
|cos|, i.e. b·μ_n avoids the cancellation band near p/4, 3p/4)?  i.e.

  Q1  COUNT: #{ y : |cos(2π b y/p)| < ε } at worst b* vs typical b.  Is the worst-b DEFICIENT
      in cancelling pairs (a "cosine-large" frequency)?  Does the deficit scale like √n or n?
  Q2  BUDGET: Σ_y 2|cos| at worst b* — compare to n (all-aligned) and to the average-b value.
      Worst-b L1-budget enrichment factor.
  Q3  THINNESS / STRUCTURE: is the set { b·y mod p : y∈μ_n } AVOIDING the cancellation band
      [p/4±δ, 3p/4±δ] more than a random same-size set?  This is the ACTUAL anti-concentration
      object (band-avoidance of the dilated subgroup), NOT a moment.

RULES: proper μ_n (n<p-1), p>>n^3, structured primes, never n=q-1, exact integer cos via the
residue r=b*y mod p and cos(2π r/p) computed in float but the COUNT thresholds use the residue.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta):
    target=int(round(n**beta)); k0=max(2,target//n)
    for dk in range(0,400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n*n*n and is_prime(p): return p
    return None

def subgroup(p,n):
    def prim_root():
        m=p-1; qs=set(); mm=m; d=2
        while d*d<=mm:
            while mm%d==0: qs.add(d); mm//=d
            d+=1
        if mm>1: qs.add(mm)
        for g in range(2,p):
            if all(pow(g,m//q,p)!=1 for q in qs): return g
    g=prim_root(); h=pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)]

def eta_mag(b,mu,p):
    s=sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in mu); return abs(s)

def cos_residues(b,mu,p):
    # |cos(2π b y/p)| over y in mu (n values; conjugate pairs give equal |cos|)
    return [abs(math.cos(2*math.pi*(b*y%p)/p)) for y in mu]

def band_avoid(b,mu,p,delta_frac=0.05):
    # fraction of b*y residues landing in the cancellation band near p/4 and 3p/4
    # (where cos ~ 0). delta_frac * p half-width.
    w=delta_frac*p
    inband=0
    for y in mu:
        r=(b*y)%p
        if abs(r-p/4)<w or abs(r-3*p/4)<w: inband+=1
    return inband/len(mu)

def run(n,beta,seed=0):
    random.seed(seed)
    p=find_prime(n,beta); mu=subgroup(p,n)
    cap=min(p-1,80000); cands=list(range(1,cap+1))
    if p-1>cap: cands+=[random.randrange(1,p) for _ in range(40000)]
    best=None;bm=-1
    for b in cands:
        m=eta_mag(b,mu,p)
        if m>bm: bm=m;best=b
    eps=0.15
    cw=cos_residues(best,mu,p)
    small_worst=sum(1 for c in cw if c<eps)
    budget_worst=sum(2*c for c in cw)/2  # Σ|cos| over n terms = Σ_y|cos|, pairs double-counted/2
    # actually Σ over all n terms of |cos|; bottom-level L1 = Σ_y 2|cos| over n/2 pairs = Σ over n terms |cos|
    budget_worst=sum(cw)
    bandw=band_avoid(best,mu,p)
    # random-b controls (average over several)
    rs_small=[]; rs_budget=[]; rs_band=[]
    for _ in range(30):
        rb=random.randrange(1,p); cr=cos_residues(rb,mu,p)
        rs_small.append(sum(1 for c in cr if c<eps))
        rs_budget.append(sum(cr))
        rs_band.append(band_avoid(rb,mu,p))
    return dict(n=n,p=p,beta=beta,worst_b=best,eta=bm,sqrt_n=math.sqrt(n),
        small_worst=small_worst, small_rand=sum(rs_small)/len(rs_small),
        budget_worst=budget_worst, budget_rand=sum(rs_budget)/len(rs_budget),
        band_worst=bandw, band_rand=sum(rs_band)/len(rs_band),
        eta_over_budget=bm/budget_worst if budget_worst>0 else 0)

if __name__=="__main__":
    print("="*100)
    print("Door-(iv) BOTTOM-LEVEL cancellation budget at worst b — band-avoidance anti-concentration")
    print("proper μ_n, p>>n^3, structured primes, never n=q-1.  eps=0.15 (|cos|<eps = cancelling term)")
    print("="*100)
    for n in (16,32,64,128):
        for beta in (4.0,4.5):
            r=run(n,beta,seed=999+n)
            print(f"\nn={n} p={r['p']} (p/n^3={r['p']/n**3:.1f}) β={beta} worst_b={r['worst_b']}")
            print(f"  |η_b*|={r['eta']:.4f}  √n={r['sqrt_n']:.3f}")
            print(f"  #cancelling terms (|cos|<0.15):  worst-b={r['small_worst']:3d}   random-b avg={r['small_rand']:.2f}   (of n={n})")
            print(f"  bottom L1 budget Σ|cos|:          worst-b={r['budget_worst']:.3f}   random-b avg={r['budget_rand']:.3f}   (max=n={n})")
            print(f"  cancellation-band occupancy:      worst-b={r['band_worst']:.4f}   random-b avg={r['band_rand']:.4f}")
            print(f"  |η|/budget = top-level coherence carry = {r['eta_over_budget']:.4f}")
    print("\n"+"="*100)
    print("VERDICT KEYS:")
    print("  Q1: is worst-b DEFICIENT in cancelling terms vs random? does deficit scale ~√n or ~n?")
    print("  Q2: worst-b budget enrichment Σ|cos| (worst vs random); how close to n (all-aligned)?")
    print("  Q3: does worst-b AVOID the cancellation band more than random (band occupancy worst<random)?")

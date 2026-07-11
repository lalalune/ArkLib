#!/usr/bin/env python3
"""
Door-IV Lane 1 PROBE v2 (sharpening) — is the d-piece multiplicative-coset coherence rho_d(b)
bounded BELOW 1 at the worst b, or can the adversary force rho_d(b)->1 even at large d?

v1 found: d=2,4 always rho=1; d=8,16 slack FLUCTUATES (0..0.17), and when nonzero the angular
spread is EXACTLY pi (two antipodal real clusters = a sign split, NOT 2D phase dispersion). Some
primes give slack=0 even at d=16 (spread=0). v2 sharpens TWO claims adversarially:

  CLAIM A (the constraint that would KILL this lever as an anti-concentration source):
    inf over a representative b-scan of rho_d(b) -> 1, i.e. for each d the WORST b drives the
    d-piece coherence arbitrarily close to 1 (spread->0). If true, no UNIFORM slack => lever dead.

  CLAIM B: whenever rho_d(b) < 1 the angular geometry is a pi-antipodal SIGN split (spread in
    {0, pi}), i.e. the pieces never form a genuine 2D fan -> the only saving is sign cancellation,
    which is exactly the index-2 negation mechanism already mapped, NOT new structure.

We scan a transversal prefix and report, per (n,p,d): (i) the ADVERSARIAL CORE quantity rho_d AT
the sampled-argmax|S| b (CORE's worst-b is argmax|S|, so this is the b that matters — NOT the
slack-friendly min-rho b), (ii) the spread there, and (iii) the angular-spread histogram over the
whole scan to test if spread ever leaves {0, pi}. The generic min_rho is kept ONLY as context and
labeled as the small-|S| cancellation regime (not CORE-relevant). For large n the prefix is a SAMPLE,
so b_smax is a lower-bound proxy for the true argmax|S| (flagged in output).
EXACT trig on the fly; PROPER mu_n; p>>n^3; never n=q-1.
"""
import cmath, math
from collections import Counter

def is_prime(p):
    if p < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if p % q == 0: return p == q
    d = p-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % p == 0: continue
        x = pow(a,d,p)
        if x==1 or x==p-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%p
            if x==p-1: ok=True; break
        if not ok: return False
    return True

def find_primes(n, count, beta=4):
    out=[]; k=(n**beta)//n+1
    while len(out)<count:
        p=k*n+1
        if is_prime(p): out.append(p)
        k+=1
    return out

def primitive_root(p):
    phi=p-1; factors=set(); m=phi; f=2
    while f*f<=m:
        if m%f==0:
            factors.add(f)
            while m%f==0: m//=f
        f+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors): return g
    raise RuntimeError

def analyze(n,p,dlist,cap):
    g0=primitive_root(p)
    g=pow(g0,(p-1)//n,p)
    elems=[1]
    for _ in range(n-1): elems.append(elems[-1]*g%p)
    tp=2*math.pi/p
    def epv(t): a=tp*(t%p); return complex(math.cos(a),math.sin(a))
    k=(p-1)//n
    cap=min(k,cap)
    def piece_stats(b,d):
        sub=n//d; pieces=[]
        for j in range(d):
            Pj=0j; idx=j
            for i in range(sub):
                Pj+=epv(b*elems[idx]); idx+=d
            pieces.append(Pj)
        S=sum(pieces); den=sum(abs(P) for P in pieces)
        rho=abs(S)/den if den>0 else 1.0
        args=[cmath.phase(P) for P in pieces if abs(P)>1e-9*den]
        if len(args)>=2:
            sa=sorted(a%(2*math.pi) for a in args)
            gaps=[sa[i+1]-sa[i] for i in range(len(sa)-1)]+[sa[0]+2*math.pi-sa[-1]]
            spread=2*math.pi-max(gaps)
        else:
            spread=0.0
        return abs(S),rho,spread
    # per d: track (i) the spread histogram over the whole scan AND (ii) the ADVERSARIAL CORE
    # quantity: rho_d at the b MAXIMIZING |S| (codex P2: min rho records the slack-FRIENDLY b, not
    # the adversarial one; CORE's worst-b is argmax|S|, so we track rho/spread THERE). We also keep
    # the generic-b min rho but label it explicitly as the cancellation regime (NOT CORE-relevant).
    dvalid=[d for d in dlist if n%d==0]
    stats={d:{'min_rho':2.0,'spreads':Counter(),
              'smax_absS':-1.0,'rho_at_smax':None,'spread_at_smax':None} for d in dvalid}
    b=1
    for t in range(cap):
        # use the d=2 split's |S| (split-independent: |S|=|sum pieces| same for any d) as the
        # |S(b)| selector; compute per-d separately for the histogram + smax tracking.
        for d in dvalid:
            absS,rho,spread=piece_stats(b,d)
            st=stats[d]
            if rho<st['min_rho']: st['min_rho']=rho
            st['spreads'][round(spread/(math.pi/4))*0.25]+=1
            if absS>st['smax_absS']:
                st['smax_absS']=absS; st['rho_at_smax']=rho; st['spread_at_smax']=spread
        b=b*g0%p
    return stats,k,cap

def main():
    print("# Door-IV multiplicative-coset coherence v2 — ADVERSARIAL CORE quantity is rho_d AT argmax|S|")
    print("# rho@smax = rho_d at the sampled-max-|S| b (CORE's worst-b); CORE needs rho@smax bounded < 1.")
    print("# spread buckets in units of pi (0=collinear, 1.0=antipodal/pi, strictly-between=genuine 2D fan)")
    print("# min_rho is the GENERIC-b cancellation regime (small |S|), NOT CORE-relevant — kept for context.")
    print()
    for n in (16,32,64):
        for p in find_primes(n,2,beta=4):
            stats,k,cap=analyze(n,p,[2,4,8,16],cap=8000)
            note=" (SAMPLED prefix; b_smax is a lower-bound proxy for the true argmax|S|)" if cap<k else ""
            print(f"n={n} p={p} m=(p-1)/n={k} scanned {cap} coset-reps{note}")
            for d in (2,4,8,16):
                if d in stats:
                    st=stats[d]
                    sp=dict(sorted(st['spreads'].items()))
                    print(f"  d={d:2d}: rho@smax={st['rho_at_smax']:.4f} spread@smax={st['spread_at_smax']/math.pi:.2f}pi |S@smax|={st['smax_absS']:.2f}"
                          f"   [generic min_rho={st['min_rho']:.4f}]  spread_hist(pi)={sp}")
            print()

if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""
Adversarial verification of the TowerSupplySubAverage finding (#389).

The finding claims:
  (A) tower direction u1=x^k -> super-code RS[k+1] = MDS = smallest list (Johnson-tight),
      its window-interior incidence is O(n), exactly 0 below delta < 1-rho-1/n.
  (B) tower deepest-band supply <= C(n,k+1) = average-term (PROVEN in Lean orchard identity).
  (C) C(n/2,j)/C(n,k+1) ~ n^{-(k+1)/2}, exponentially sub-average.
  (D) the GENUINE worst super-code MINIMIZES distance d+; above Sidon threshold
      (n-k)-d+ = O(1), giving O(1) list advantage. closed form:
      "worst list / avg-term = q^{((n-k)-d+)}".
  (E) therefore: removes tower as counterexample; SUPPORTS average-term.

We adversarially test:
  1. Is the tower super-code RS[k+1] actually MDS / smallest list?  (claim A) -- direct.
  2. Is "deepest-band supply" the right band for the WINDOW INTERIOR?  (band confusion)
  3. Does a low-distance super-code (the claimed real worst) actually give only O(1)
     more incidence than the MONOMIAL super-code, in q>>n window-interior?  (claim D,E)
     -- THIS is the load-bearing claim.  Construct minimum-coset-weight u1 and measure.
"""
import itertools, random
from math import comb, sqrt, log

def rou(q,n):
    """eval domain mu_n = n-th roots of unity in F_q (n | q-1)."""
    for g in range(2,q):
        x=1;s=set()
        for _ in range(q-1): x=x*g%q;s.add(x)
        if len(s)==q-1:
            o=pow(g,(q-1)//n,q);return [pow(o,i,q) for i in range(n)]
    return None

def inv(a,q): return pow(a,q-2,q)

def interp_fit(pts_idx, mu, vals, q, k):
    res=[0]*len(mu)
    for t in range(len(mu)):
        xt=mu[t]; acc=0
        for j in range(k):
            num=1;den=1
            for l in range(k):
                if l!=j:
                    num=num*(xt-mu[pts_idx[l]])%q; den=den*(mu[pts_idx[j]]-mu[pts_idx[l]])%q
            acc=(acc+vals[pts_idx[j]]*num*inv(den,q))%q
        res[t]=acc
    return res

def maxagree(mu,vals,q,k,n):
    best=0
    for sub in itertools.combinations(range(n),k):
        f=interp_fit(sub,mu,vals,q,k)
        c=sum(1 for i in range(n) if f[i]==vals[i])
        if c>best: best=c
    return best

def coset_min_weight(mu,u1,q,k,n):
    """min Hamming weight of u1 + RS[k] = n - maxagree(u1, RS[k]).  = distance of u1 to code."""
    return n - maxagree(mu,u1,q,k,n)

def nbad(mu,u0,u1,q,k,n,a):
    c=0
    for g in range(q):
        v=[(u0[i]+g*u1[i])%q for i in range(n)]
        if maxagree(mu,v,q,k,n)>=a: c+=1
    return c

def first_moment_avg(n,k,q,a):
    """The 'average-term' first moment of the incidence at agreement a.
       #bad = E_gamma[#codewords agreeing >= a].  For a random target the
       expected # of RS[k+1] codewords at agreement >= a:
       (codewords in RS[k+1] super-code) * P(random word agrees >= a coords).
       Average-term = q * C(n,a) * (q-1)^? ... we use the heuristic FIRST MOMENT
       count of (k+1)-subset interpolants = C(n,a) over the relevant scaling.
       For the deepest band a=k+1 the finding identifies average = C(n,k+1)."""
    return comb(n,a)

print("="*78)
print("CLAIM C numeric: C(n/2,j)/C(n,k+1) for prize-scale n,k")
print("="*78)
for n,k in [(1024,512),(256,128),(64,32),(32,16)]:
    kk=k+1
    if kk%2!=0:
        kk2=kk  # use k+1 even-ish; for ratio just take j=(k+1)//2
    j=(k+1)//2
    num=comb(n//2,j)
    den=comb(n,2*j)
    print(f" n={n} k={k}: C(n/2,{j})={num:.3e}  C(n,{2*j})={den:.3e}  ratio={num/den:.3e}  "
          f"n^(-(k+1)/2)={n**(-(k+1)/2):.3e}")
print()

print("="*78)
print("CLAIM A: is tower super-code RS[k+1] = MDS = SMALLEST list?")
print("  monomial dir x^k -> super-code RS[k+1].  Check its window-interior incidence")
print("  vs the MIN-DISTANCE (low-distance) direction u1 (claimed real worst), q>>n.")
print("="*78)

def run(q,n,k,w,nsamp=80,seed=1):
    mu=rou(q,n)
    if mu is None:
        print(f"  no full mu_n for q={q} n={n}"); return
    a=n-w; J=1-(k/n)**0.5; d=w/n; rho=k/n
    monwords=[[pow(mu[i],e,q) for i in range(n)] for e in range(n)]
    # MONOMIAL pencil incidence (super-code = RS[k+1] = MDS): use x^k as direction.
    u1mono=monwords[k]
    distmono=coset_min_weight(mu,u1mono,q,k,n)
    Imono=0; u0best=None
    rng=random.Random(seed)
    # search over offsets u0 to maximize incidence of the monomial direction
    for _ in range(nsamp):
        u0=[rng.randrange(q) for _ in range(n)]
        nb=nbad(mu,u0,u1mono,q,k,n,a)
        if nb>Imono: Imono=nb
    # also try monomial offsets
    for b in range(n):
        nb=nbad(mu,monwords[b],u1mono,q,k,n,a)
        if nb>Imono: Imono=nb
    # MIN-DISTANCE direction search: find u1 (not in code) with SMALLEST coset-min-weight,
    # i.e. closest to code -> claimed worst. Search random + structured candidates.
    best_lowdist=None; best_lowdist_w=n+1
    cands=[]
    # random candidates
    for _ in range(40):
        u1=[rng.randrange(q) for _ in range(n)]
        cands.append(u1)
    # structured: codeword + single spike (distance ~ 1 from code but spike makes it far-ish)
    for spikeval in [1,2]:
        for pos in range(min(n,6)):
            base=monwords[0][:]  # constant codeword in RS[k]
            u1=base[:]
            u1[pos]=(u1[pos]+spikeval)%q
            cands.append(u1)
    # monomial near-code: x^k itself already. add a few low-degree-excess words
    for u1 in cands:
        dw=coset_min_weight(mu,u1,q,k,n)
        if dw>=1 and dw<best_lowdist_w:  # must be FAR (not in code): dw>=1; want minimal but still a real direction
            # require it's a genuine far direction for radius w: agreement of u1 < a
            if maxagree(mu,u1,q,k,n) < a:
                best_lowdist_w=dw; best_lowdist=u1
    Ilow=0
    if best_lowdist is not None:
        for _ in range(nsamp):
            u0=[rng.randrange(q) for _ in range(n)]
            nb=nbad(mu,u0,best_lowdist,q,k,n,a)
            if nb>Ilow: Ilow=nb
        for b in range(n):
            nb=nbad(mu,monwords[b],best_lowdist,q,k,n,a)
            if nb>Ilow: Ilow=nb
    avg=first_moment_avg(n,k,q,a)
    print(f" n={n} q={q} k={k} rho={rho:.3f} q/n={q/n:.0f}  w={w} d={d:.3f} ({'ABOVE-J' if d>J else 'below-J'} J={J:.3f}) a={a}")
    print(f"   MONOMIAL (x^k, dist={distmono}, MDS-route): I_mono = {Imono}  inc/q={Imono/q:.4f}")
    print(f"   MIN-DIST direction (coset-wt={best_lowdist_w}): I_low = {Ilow}  inc/q={Ilow/q:.4f}")
    print(f"   ratio I_low/I_mono = {Ilow/max(Imono,1):.3f}   [claim D/E: should be O(1)]")
    print(f"   C(n,a) first-moment-ish avg = {avg}")
    print()

# window-interior, q>>n cases (small enough to brute force maxagree, C(n,k))
# RS[mu_8,k=4]/F_257: rho=0.5, window (1-sqrt.5, 1-.5)=(0.293,0.5). w=3 -> d=0.375 in window.
run(257,8,4,3,nsamp=60,seed=2)
# RS[mu_12,k=4]/F_61: from finding's own example
run(61,12,4,5,nsamp=60,seed=3)
run(61,12,4,4,nsamp=60,seed=4)
# deeper q>>n: RS[mu_8,k=3]/F_257 rho=.375 window(.388,.625)
run(257,8,3,3,nsamp=60,seed=5)

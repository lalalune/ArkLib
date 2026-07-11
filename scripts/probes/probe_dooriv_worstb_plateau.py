#!/usr/bin/env python3
"""
Door-(iv) Lane 1 sweep 2 — is the sup-norm a SHARP SPIKE or a BROAD PLATEAU over coset reps?

The brief: "what arithmetic of b selects the worst coset alignment? is the worst-b set itself
structured?" A complementary cut to the worst-b-quotient-arithmetic probe (1e22ed805, found
scattered/gcd=1) and the spatial-spread probe (758205014, energy-blind): characterize the
DISTRIBUTION of |eta_b| over coset representatives, specifically the GAP between the top period
and the bulk.

Why this matters for door (iv): a b-side ANTI-CONCENTRATION lever (bounding the worst |eta_b| by
controlling how many b achieve near-worst) only has grip if the sup is an ISOLATED spike that the
arithmetic of b pins down. If instead a large FRACTION of cosets achieve within (1-o(1)) of the
sup (broad plateau), then the worst-b is generic, there is NO special arithmetic selecting it, and
any "worst-b is structured" hope is dead — the sup is a typical large deviation, routing back to
the moment/energy distribution of |eta_b| (the BGK wall), not a special coset.

Measured per (n,p), over ALL (p-1)/n coset representatives where feasible (else a large sample):
  - M = max |eta_b|, and the empirical distribution of |eta_b|/M
  - frac90 = fraction of cosets with |eta_b| >= 0.9*M   (plateau width near the top)
  - frac75 = fraction with |eta_b| >= 0.75*M
  - top-gap = (M - second_distinct_M) / M               (spike sharpness)
  - mean/M and (max-mean)/std  (how many std above the mean the sup sits = large-deviation depth)

EXACT complex eta, PROPER mu_n, p >> n^3, never n=q-1.
"""
import cmath, math, random, statistics

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
            if p>n and is_prime(p): return p
    return None

def subgroup(p,n):
    pm1=p-1; f={}; m=pm1; d=2
    while d*d<=m:
        while m%d==0: f[d]=1; m//=d
        d+=1
    if m>1: f[m]=1
    def isg(g): return all(pow(g,pm1//q,p)!=1 for q in f)
    g=2
    while not isg(g): g+=1
    h=pow(g,pm1//n,p); mu=[]; c=1
    for _ in range(n): mu.append(c); c=c*h%p
    return mu, g

def eta(b,mu,p):
    return abs(sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in mu))

def coset_reps(p,n,g):
    """One representative per multiplicative mu_n-coset: g^j for j=0..(p-1)/n - 1.
    These are exactly the distinct coset reps since g generates F_p* and mu_n = <g^{(p-1)/n}>."""
    ncos=(p-1)//n
    reps=[]; cur=1
    for j in range(ncos):
        reps.append(cur); cur=cur*g%p
    return reps

def main():
    random.seed(99)
    print("=== worst-b plateau vs spike over coset reps (proper mu_n) ===")
    print(f"{'n':>4} {'p':>10} {'#cos':>7} {'M/sqn':>6} {'frac>=.9M':>9} {'frac>=.75M':>10} "
          f"{'topgap':>7} {'mean/M':>7} {'(M-mu)/sd':>9}")
    for n,beta in [(16,4.0),(32,4.0),(64,4.0),(16,4.5),(32,4.5)]:
        p=find_prime(n,beta)
        if p is None: continue
        mu,g=subgroup(p,n)
        reps=coset_reps(p,n,g)
        ncos=len(reps)
        # cap work
        if ncos>20000:
            reps=random.sample(reps,20000)
        vals=[eta(b,mu,p) for b in reps]
        M=max(vals); sqn=math.sqrt(n)
        f90=sum(1 for v in vals if v>=0.9*M)/len(vals)
        f75=sum(1 for v in vals if v>=0.75*M)/len(vals)
        svals=sorted(set(round(v,6) for v in vals),reverse=True)
        topgap=(svals[0]-svals[1])/svals[0] if len(svals)>1 else 0.0
        mu_=statistics.mean(vals); sd=statistics.pstdev(vals)
        dev=(M-mu_)/sd if sd>0 else float('inf')
        print(f"{n:>4} {p:>10} {ncos:>7} {M/sqn:>6.2f} {f90:>9.4f} {f75:>10.4f} "
              f"{topgap:>7.4f} {mu_/M:>7.3f} {dev:>9.2f}")

if __name__=="__main__":
    main()

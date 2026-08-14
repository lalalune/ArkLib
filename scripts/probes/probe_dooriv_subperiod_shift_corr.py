#!/usr/bin/env python3
"""
door-(iv) Lane-1 PROBE — joint extreme correlation of the two-dilate sub-period sum.

Dilation form (just kerneled, 223b4c0d2): prize H(n) = max_b (S(b)+S(gb)), where
S(c) = |eta ψ μ_{n/2} c| is the sub-period magnitude and g is the index-2 coset rep (a generator
of μ_n, g∉μ_{n/2}).  S is μ_{n/2}-coset-invariant in c; the shift c->gc moves to the SIBLING
μ_{n/2}-coset inside the same μ_n-coset.

QUESTIONS (un-probed; the white-field autocorr was on the FULL period η over the μ_n-quotient,
NOT on the SUB-period S over the μ_{n/2}-quotient under the specific generator shift g):
  Q1. At the prize-worst b* = argmax(S(b)+S(gb)): are BOTH halves near their individual maxima
      (positively-correlated joint extreme => prize ≈ 2·max S), or does the argmax exploit a
      "one big + one medium" asymmetry?  Report S(b*)/maxS and S(gb*)/maxS.
  Q2. Is the shift-g autocorrelation of S structured?  Compare H = max_b(S(b)+S(gb)) to:
        - 2*maxS               (perfect positive joint extreme)
        - maxS + median S      (one-big-one-typical)
        - an i.i.d. surrogate: max over random independent pairing of the SAME S-multiset.
      If H/(2 maxS)->1 the two dilates co-peak (no slack); if H ~ iid-surrogate the shift is
      structureless; if H sits strictly between, there is exploitable shift structure.

probe-first, EXACT C, PROPER 2-power μ_n, p>>n^3, m=(p-1)/n>1, structured+generic primes, FULL F_p*
sub-period scan at n=16/32, sampled larger, NEVER n=q-1.
"""
import cmath, math, random, statistics
def isp(x):
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return x>1
def fac(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f
def proot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def run(p,n,full,samples=5000):
    w=2*math.pi/p; EP=lambda t: cmath.exp(1j*w*(t%p))
    g=proot(p); m=(p-1)//n
    gen_n=pow(g,(p-1)//n,p)          # generator of μ_n
    half=n//2; z=pow(gen_n,2,p)      # generator of μ_{n/2}
    H=[]; cur=1
    for _ in range(half): H.append(cur); cur=cur*z%p
    # S(c) = |Σ_{y∈H} e_p(c y)| ; iterate c over coset reps of μ_n (c=g^j)
    reps=[]
    if full or m<=samples:
        cur=1
        for _ in range(m): reps.append(cur); cur=cur*g%p
    else:
        seen=set()
        while len(reps)<samples:
            j=random.randrange(m)
            if j in seen: continue
            seen.add(j); reps.append(pow(g,j,p))
    def S(c): return abs(sum(EP((c*y)%p) for y in H))
    # for each rep b, the two dilates are b and gen_n*b (the index-2 coset rep is gen_n)
    pairs=[]
    Svals=[]
    for b in reps:
        sb=S(b); sgb=S((gen_n*b)%p)
        pairs.append((sb+sgb, sb, sgb)); Svals.append(sb)
    pairs.sort(key=lambda r:-r[0])
    Hn,sb_star,sgb_star = pairs[0]
    maxS=max(Svals); medS=statistics.median(Svals)
    sn=math.sqrt(n)
    # iid surrogate: max over random independent pairing of S-multiset
    rs=Svals[:]; best_iid=0
    for _ in range(20000):
        a=random.choice(rs); b2=random.choice(rs)
        if a+b2>best_iid: best_iid=a+b2
    return (m, Hn/sn, sb_star/maxS, sgb_star/maxS, (2*maxS)/sn, (maxS+medS)/sn, best_iid/sn, Hn/(2*maxS))
PR={16:[65537,188417,1179649],32:[163841,1179649],64:[401537,786433]}
print("dilation-form joint extreme: H(n)=max_b(S(b)+S(gb)) vs 2maxS, maxS+medS, iid-surrogate")
print("cols: H/√n | S(b*)/maxS S(gb*)/maxS | 2maxS/√n | (maxS+medS)/√n | iidSurr/√n | H/(2maxS)")
for n in (16,32,64):
    for p in PR[n]:
        if not isp(p) or (p-1)%n: continue
        full=(n in (16,32) and p<300000)
        m,Hsn,r1,r2,two,mm,iid,ratio=run(p,n,full)
        tag="FULL" if full else "samp"
        print(f" n={n:2} p={p:8} m={m:6} [{tag}] H/√n={Hsn:.3f} | {r1:.3f} {r2:.3f} | 2maxS/√n={two:.3f} | maxS+med={mm:.3f} | iid={iid:.3f} | H/2maxS={ratio:.3f}")

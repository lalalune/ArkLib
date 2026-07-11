#!/usr/bin/env python3
"""
door-(iv) Lane-1 — NON-negation-stable split coherence: ADVERSARIAL re-check (part b).

Part (a) found: arc splits of mu_n that BREAK x->-x symmetry STILL saturate worst-b
rho->1 (ARC2 1-rho -> 0 with p; finer arcs ARC4/8 have small NON-growing slack). To make
the refutation honest we hit it with the toughest variants:
  (1) NON-CONTIGUOUS non-negation-stable splits: bit-pattern of exponent j (LSB, gray-code,
      random fixed asymmetric subset) — not arcs, to rule out "it's an arc artifact".
  (2) STRUCTURED Fermat-type primes (large v2(p-1), incl p=65537=F4) — to rule out
      "generic primes only".
  (3) report whether worst-b 1-rho GROWS with n for ANY fixed split (a growing slack
      would be the live lever; a shrinking/flat one kills it).
All in prize regime: PROPER thin mu_n (n=2^a), p=1 mod n, p>>n^3, NEVER n=q-1, exact C.
"""
import cmath, math, random

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for _ in range(20):
        a=random.randrange(2,n-1);x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True

def factorize(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f

def primitive_root(p):
    fac=factorize(p-1)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac):return a
    raise RuntimeError

def find_prime(n,beta,structured=False,tries=400000):
    target=int(n**beta);base=(target//n)*n+1
    best=None
    for k in range(tries):
        p=base+k*n
        if p>n**3 and p%n==1 and is_prime(p):
            if not structured: return p
            # structured: maximize v2(p-1)
            v=0;t=p-1
            while t%2==0:t//=2;v+=1
            if v>=int(math.log2(n))+3:
                return p
    return best

def v2(x):
    v=0
    while x%2==0:x//=2;v+=1
    return v

def run(n,beta,structured=False):
    p=find_prime(n,beta,structured)
    if p is None:
        print(f"  n={n} beta={beta} struct={structured}: no prime"); return None
    m=(p-1)//n
    assert p%n==1 and p>n**3 and n!=p-1
    pr=primitive_root(p);g0=pow(pr,(p-1)//n,p)
    mu=[pow(g0,j,p) for j in range(n)]
    w=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
    creps=list(range(m))
    if m>20000: creps=random.sample(creps,20000)
    rnd=random.Random(12345)
    asym=set(rnd.sample(range(n), n//2 -1))  # asymmetric: |asym| != n/2 so not negation-pairable cleanly
    def split_lsb():   # by LSB of j: even/odd -> THIS is the subgroup ref (negation-stable), skip
        return None
    def split_bit1():  # by bit-1 of j (j//2 %2): NOT a coset, breaks symmetry
        P=[[],[]]
        for j in range(n): P[(j>>1)&1].append(j)
        return P
    def split_gray():  # gray-code high bit
        P=[[],[]]
        for j in range(n):
            gcode=j^(j>>1)
            P[(gcode*2)//n].append(j) if False else P[1 if gcode>=n//2 else 0].append(j)
        return P
    def split_asym():  # fixed asymmetric subset (|P0|=n/2-1)
        P=[[],[]]
        for j in range(n): P[1 if j in asym else 0].append(j)
        return P
    splits={"BIT1":split_bit1(),"GRAY":split_gray(),"ASYM(n/2-1)":split_asym()}
    worst={k:0.0 for k in splits}
    for c in creps:
        b=pow(pr,c,p)
        terms=[w[(b*mu[j])%p] for j in range(n)]
        for name,P in splits.items():
            ps=[sum(terms[j] for j in idx) for idx in P]
            den=sum(abs(s) for s in ps)
            if den>1e-12:
                rho=abs(sum(ps))/den
                if rho>worst[name]: worst[name]=rho
    tag="STRUCT" if structured else "generic"
    print(f"  n={n:3d} p={p:>12d} v2(p-1)={v2(p-1):2d} m={m:>9d} beta={math.log(p)/math.log(n):.2f} [{tag}] scanned={len(creps)}")
    out={}
    for name in splits:
        print(f"      worst rho [{name:12s}] = {worst[name]:.6f}  (1-rho={1-worst[name]:.2e})")
        out[name]=1-worst[name]
    return out

if __name__=="__main__":
    print("=== NON-negation-stable split coherence: adversarial re-check (non-arc + structured) ===\n")
    print("-- generic primes, growth-in-n check --")
    res={}
    for n in (16,32,64):
        r=run(n,3.9,structured=False)
        if r:
            for k,v in r.items(): res.setdefault(k,[]).append((n,v))
    print("\n-- structured Fermat-type primes (large v2) --")
    for n in (16,32,64):
        run(n,4.0,structured=True)
    print("\n-- 1-rho vs n (does ANY split give GROWING slack? growing => live lever) --")
    for k,seq in res.items():
        s=" ".join(f"n{n}:{v:.1e}" for n,v in seq)
        grow = seq[-1][1] > seq[0][1]*1.5
        print(f"   {k:12s} {s}   GROWING={grow}")

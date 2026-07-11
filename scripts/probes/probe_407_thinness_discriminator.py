#!/usr/bin/env python3
"""
probe_407_thinness_discriminator.py  (#407)

Search for a THINNESS-DISCRIMINATING object: one whose certifying quantity is
BOUNDED in the thin prize window (beta~4-5) but GROWS / mis-behaves in the thick
window (beta~2.3-3.2). Per rule 3 the prize lever must be such an object; the moment
certificate provably is NOT (thickness-invariant slack, prior probe 82581fb79).

Two candidate discriminators tested over PROPER mu_n < F_p^* (exact FFT):

(D1) The NORMALIZED prize ratio
        R(n,p) = M(n) / ( sqrt(n) * sqrt(log(p/n)) )
     The prize is R <= C absolute. Question: is R BOUNDED/decreasing as beta grows
     into the thin window, but LARGER/growing in the thick window? A discriminator
     would show R(thin) clearly < R(thick) at matched n -- i.e. the prize normalization
     sqrt(log(p/n)) is the RIGHT scale only in thin.

(D2) The Sidon/additive-structure depth signature. mu_n is claimed B_infinity-Sidon to
     depth ~log n (W_r = 0 for r <= ell). Measure the FIRST nonzero additive moment:
        for r=1,2,3,...: count r-fold additive coincidences within mu_n that are NOT
        forced (the "excess" representation count). The depth ell where excess first
        appears -- does ell scale with thinness (grows as p/n grows = thinner relative
        to field) vs saturate in thick? A thinness signature: deeper Sidon-ness in thin.
"""
import math, cmath

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def factor_small(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def find_prime(target, mod_n):
    k=max(1,round(target/mod_n))
    for delta in range(0,400000):
        for s in (1,-1):
            kk=k+s*delta
            if kk<1: continue
            p=kk*mod_n+1
            if p>3 and is_prime(p): return p
    return None

def subgroup(n,p):
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e

def Msup(elts,p):
    w=2*math.pi/p; best=0.0
    for b in range(1,p):
        s=0j
        for xx in elts: s+=cmath.exp(1j*w*((b*xx)%p))
        a=abs(s)
        if a>best: best=a
    return best

def sidon_depth(elts,p):
    """First r where mu_n fails to be a perfect B_r-Sidon set additively in F_p:
       i.e. smallest r such that some value has MORE than the trivially-forced number
       of ordered r-term representations sum of r elements (with the symmetric
       multiplicity). We measure the max EXCESS multiplicity of r-fold sumset.
       Report the multiplicity profile; 'depth' = largest r with no nontrivial collision
       beyond the symmetric baseline."""
    S=list(elts); n=len(S)
    res={}
    # r=2: count representations of each value as a+b (ordered). Sidon (B_2) => each
    # value has <=2 ordered reps (a+b,b+a) unless a==b. Excess = collisions.
    from collections import Counter
    depth=0
    for r in range(2,5):
        c=Counter()
        # ordered r-fold sums mod p (only feasible for small n,r)
        if n**r > 2_000_000:
            return depth, f"r={r} too big to enumerate (n^r={n**r})"
        def rec(idx,acc):
            if idx==r:
                c[acc%p]+=1; return
            for x in S: rec(idx+1,acc+x)
        rec(0,0)
        # baseline: a B_r-Sidon set has all r-subset-sums distinct => for DISTINCT
        # multisets each value's count = (number of ordered arrangements). Excess =
        # max count minus the count attributable to a single multiset's permutations.
        # Simpler discriminator: number of DISTINCT values vs total n^r. Perfect Sidon
        # (no nontrivial coincidences) maximizes distinct values.
        distinct=len(c)
        maxmult=max(c.values())
        # fraction of "wasted" mass = 1 - distinct/n^r (lower = more Sidon-like)
        waste=1.0-distinct/(n**r)
        res[r]=(distinct,maxmult,waste)
    return res

def run():
    print("THINNESS-DISCRIMINATOR search (proper mu_n < F_p^*, exact)\n")
    print("D1: R(n,p)=M(n)/(sqrt(n)*sqrt(log(p/n))) -- prize wants R<=C absolute.\n")
    for n in [8,16]:
        print(f"==== n={n} ====")
        betas=[2.3,2.7,3.2,3.6,4.0,4.5] if n==8 else [2.3,2.7,3.0,3.3,3.6]
        rows=[]
        for beta in betas:
            p=find_prime(int(n**beta),n)
            if not p: continue
            ab=math.log(p)/math.log(n)
            e=subgroup(n,p)
            M=Msup(e,p)
            denom=math.sqrt(n)*math.sqrt(max(1e-9,math.log(p/n)))
            R=M/denom
            rows.append((ab,p,M,R))
            print(f"  beta={ab:.2f} p={p}: M={M:.3f}  M/sqrt(n)={M/math.sqrt(n):.3f}  R={R:.4f}")
        # discriminator readout: is R(thin) < R(thick)?
        if len(rows)>=2:
            thick=[r for r in rows if r[0]<3.3]; thin=[r for r in rows if r[0]>=3.9]
            if thick and thin:
                Rt=sum(r[3] for r in thick)/len(thick); Rn=sum(r[3] for r in thin)/len(thin)
                print(f"  >> avg R thick(beta<3.3)={Rt:.4f}  thin(beta>=3.9)={Rn:.4f}  "
                      f"discriminates={'YES (thin<thick)' if Rn<Rt-0.02 else 'no (R flat/rising)'}")
        print()

    print("\nD2: Sidon depth signature (waste=1-distinct/n^r; lower => more Sidon-like)\n")
    for n in [8,16]:
        for beta in [2.5, 4.0]:
            p=find_prime(int(n**beta),n)
            if not p: continue
            ab=math.log(p)/math.log(n)
            e=subgroup(n,p)
            d=sidon_depth(e,p)
            print(f"  n={n} beta={ab:.2f} p={p}: {d}")

if __name__=="__main__":
    run()

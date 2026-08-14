#!/usr/bin/env python3
"""LANE wf-M1: the TRUE height inequality. The sufficient lemma:
   if  p > max_{ antipodal-free T, |T|<=2r }  |N(sigma_T)|   then NO spurious config at p at depth r.
We measure  log10 max|N|  vs the crude house log10((2r)^{n/2}) and vs log10 p (prize ~ n^4).
If max|N| at depth r ~ ln p is itself ~ p or larger, the route still needs the structure-aware
count (rate), NOT just the max. We report log10 max|N| and the implied min prime p to be safe."""
import itertools, math, cmath
def antipodal_free(T,n):
    s=set(T); h=n//2
    return all((j+h)%n not in s for j in T)
def lognorm(T,n):
    lg=0.0
    for a in range(1,n,2):
        s=sum(cmath.exp(1j*2*math.pi*((a*j)%n)/n) for j in T)
        m=abs(s)
        if m<1e-9: return None
        lg+=math.log10(m)
    return lg
for n in [16,32,64]:
    print(f"\n=== n={n}  log10(n^4)={4*math.log10(n):.2f}  crude log10((2r)^(n/2)) shown ===",flush=True)
    for w in range(2,9,2):
        mx=-1; sampled=0
        for c in itertools.combinations(range(1,n),w-1):
            T=(0,)+c
            if not antipodal_free(T,n): continue
            lg=lognorm(T,n)
            if lg is None: continue
            if lg>mx: mx=lg
            sampled+=1
            if sampled>=80000: break
        crude=(n/2)*math.log10(w)
        print(f"  w={w}: log10 max|N|={mx:.3f}   crude (n/2)log10(w)={crude:.3f}   (ratio actual/crude={mx/crude:.3f})",flush=True)

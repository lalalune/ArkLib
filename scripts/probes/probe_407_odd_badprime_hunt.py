# Is 2 the ONLY bad prime? For n=16,m=2,r=4: over F_{p^d} (mu_16 ⊆ F_{p^d}),
# does any gap-valid config have e_m OUTSIDE the genuine sumset? If no odd p is bad => D=2^k.
import sympy as sp
from itertools import combinations
import numpy as np

n=16; m=2; r=4; HALF=n//2; size=r*m
gap=[i for i in range(1,2*m) if i!=m]; needed=sorted(set(gap+[m]))
subs=list(combinations(range(n),size))
# exact Z[zeta_16] vectors (len 8) per subset per i
V={i:[] for i in needed}
for S in subs:
    for i in needed:
        vec=[0]*HALF
        for c in combinations(S,i):
            T=sum(c)%n
            if T<HALF: vec[T]+=1
            else: vec[T-HALF]-=1
        V[i].append(vec)
# C-genuine configs (gap vectors all zero) and their e_m vectors = sumset
zmask=[all(v==0 for v in V[i][s] for i_ in [i]) for s in range(len(subs))]  # placeholder
zmask=[all(all(c==0 for c in V[i][s]) for i in gap) for s in range(len(subs))]
sumset_vecs=[V[m][s] for s in range(len(subs)) if zmask[s]]
Ccount=len({tuple(v) for v in sumset_vecs})
print(f"n={n} m={m} r={r}: C-sumset size |H^(+r)|={Ccount}, #subsets={len(subs)}")

y=sp.symbols('y')
Phi=sp.cyclotomic_poly(n,y)
def vec_to_poly(vec): return sum(int(c)*y**l for l,c in enumerate(vec))

bad=[]
for p in sp.primerange(3,120):
    if p==2: continue
    facs=sp.Poly(Phi,y,modulus=p).factor_list()[1]
    # each factor h gives an embedding mu_16 -> F_p[y]/h
    prime_bad=False; detail=None
    for (hpoly,mult) in facs:
        h=hpoly  # Poly over GF(p)
        def red(vec):
            return sp.Poly(vec_to_poly(vec),y,modulus=p) % h
        # sumset values reduced in this field
        Sig={ tuple(sp.Poly(red(v),y,modulus=p).all_coeffs()) for v in sumset_vecs }
        # gap-valid configs in this field: red(V[i])==0 for i in gap
        for s in range(len(subs)):
            ok=True
            for i in gap:
                if red(V[i][s]) != sp.Poly(0,y,modulus=p):
                    ok=False; break
            if ok:
                em=tuple(sp.Poly(red(V[m][s]),y,modulus=p).all_coeffs())
                if em not in Sig:
                    prime_bad=True; detail=(int(p),h.degree(),s); break
        if prime_bad: break
    if prime_bad:
        bad.append(detail)
        print(f"  p={p}: BAD (deg-{detail[1]} factor, config {detail[2]} gives e_m OUTSIDE sumset)")
    else:
        pass
print("\nODD BAD PRIMES in [3,120):", bad if bad else "NONE  ==>  D is a pure power of 2  ==>  q (odd, =1 mod n) never divides D  ==>  bound holds at the prize prime")

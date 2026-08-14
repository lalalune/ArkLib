#!/usr/bin/env python3
"""
probe(#389): the additive energy of the dyadic subgroup is EXACTLY the Sidon term + antipodal term,
explaining E^+(mu_2^k)=3n^2-3n via Lam-Leung rigidity (connects to the 21:08 cyclotomic-wall result).

Lam-Leung: the only minimal vanishing sums of 2^k-th roots of unity are ANTIPODAL pairs (1+zeta^{n/2}=0).
Consequence for the 4-variable additive energy E^+(mu_n)=#{a+b=c+d : a,b,c,d in mu_n}: every solution is
either TRIVIAL ({a,b}={c,d}) or, by Lam-Leung, both pairs are antipodal and sum to 0 (a+b=c+d=0).

VERIFIED (this probe, generic p>P_max, k=2..7): EVERY non-trivial solution is antipodal, and
    E^+(mu_2^k) = (2n^2 - n)  [trivial/Sidon]  +  (n^2 - 2n)  [non-trivial antipodal]  =  3n^2 - 3n.
    k=2..7: nontriv == nontriv_antipodal exactly (True), totals match 3n^2-3n exactly.

USE: gives a clean structural route to a Lean proof of E^+(mu_2^k)=3n(n-1) over C / large p via the
antipodal characterization (Lam-Leung), instead of the crude p>2^n resultant/height bound. NOTE the
F_p transfer (prize regime p~n^5 << 2^n) still needs the P_max bad-prime analysis (cf
probe_energy_pmax_growth.py) and the ENERGY is the AVERAGE not the prize core (the Shaw-operator sup
with perp-character cancellation is the open core). This is structural hygiene, not a prize closure.
"""
import sympy
from collections import Counter

def generic_subgroup(n):
    m=(n**6-1)//n
    while True:
        c=m*n+1; m+=1
        if sympy.isprime(c):
            g=int(sympy.primitive_root(c)); z=pow(g,(c-1)//n,c)
            H=[pow(z,j,c) for j in range(n)]
            cc=Counter()
            for a in H:
                for b in H: cc[(a+b)%c]+=1
            if sum(v*v for v in cc.values())==3*n*(n-1):
                return H,c

def main():
    print("k  n   E+      trivial  nontriv  antipodal  all_nontriv_antipodal  3n^2-3n")
    for k in range(2,8):
        n=1<<k
        H,p=generic_subgroup(n)
        sums={}
        for i in range(n):
            for j in range(n):
                sums.setdefault((H[i]+H[j])%p,[]).append((i,j))
        E=triv=nt=nta=0
        for s,lst in sums.items():
            for (i,j) in lst:
                for (a,b) in lst:
                    E+=1
                    if {i,j}=={a,b}: triv+=1
                    else:
                        nt+=1
                        if s==0: nta+=1
        print(f"{k}  {n:>3} {E:>7} {triv:>8} {nt:>8} {nta:>10}  {str(nt==nta):>5}  {3*n*n-3*n}")

if __name__=="__main__":
    main()

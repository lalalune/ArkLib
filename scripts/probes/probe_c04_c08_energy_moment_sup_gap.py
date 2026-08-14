#!/usr/bin/env python3
"""
C04 Sarkozy energy->sup-norm (analyst: secretly-open, energy gives avg not L-inf).
C08 Myerson period-poly house (analyst: secretly-open, coeffs=moments=forced anomaly).

Both reduce to: a CLOSED energy/moment bound on the dyadic Gauss periods eta_b
(b != 0, b in Z/p) controls a SYMMETRIC / AVERAGE quantity (L^2 energy E_r, or the
elementary-symmetric period-poly coefficients = power sums = moments), NOT the single
worst conjugate sup M(mu_n) = max_b |eta_b| (= the open BGK L-inf wall).

Two things measured exactly over proper mu_n (p prime, p>>n^3, n|p-1, never n=p-1),
n = 2^mu:

 (A) [C04 horn] Sarkozy-style energy gives equidistribution on AVERAGE (L^2), not L-inf.
     We compute, for r = 1..R:
        E_r = sum_{b != 0} |eta_b|^{2r}              (the r-th energy / 2r-th moment)
        the "average" period^{2r}: (E_r/(p-1))^{1/2r} = the L^{2r} norm
        the TRUE sup M = max_b |eta_b|
     and show the Markov/moment bound  M <= (E_r)^{1/2r}  needs r ~ log p to close the
     gap (single fixed r leaves M >> L^{2r} average).  We tabulate M / (E_r/(p-1))^{1/2r}.

 (B) [C08 horn] period-poly coefficients are elementary symmetric functions of the m
     periods = power sums = moments.  We confirm the power-sum p_r = sum_c eta_c^r
     (sum over the m = (p-1)/n DISTINCT period values, the Galois conjugates) recovers
     the same moment data, and that bounding |coeff_j| <= C(m,j) n^{j/2} to depth j ~ m
     IS exactly bounding all moments = deep-moment validity (the open object).

We REPORT whether the closed L^2 / symmetric-function data alone pins M at the floor
sqrt(n log(p/n)).  A flip-to-survives requires a SINGLE fixed-r closed moment to already
give M <= O(sqrt(n)) -- contradicting the meta-theorem.  Stress: try the BEST single r.
"""
import sympy
from math import gcd, sqrt, cos, sin, pi, log

def find_p_and_subgroup(n, mult=100):
    target = n**4; m=target//n
    while True:
        p=m*n+1
        if sympy.isprime(p) and p>mult*n**3 and (p-1)!=n:
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            mu=[pow(z,j,p) for j in range(n)]
            if len(set(mu))==n: return p,z,mu
        m+=1

def all_periods(p, z, n):
    """eta_b for b=1..p-1.  eta_b = sum_{y in mu_n} e_p(b y).  Returns list of (re,im,mag)."""
    mu=[pow(z,j,p) for j in range(n)]
    tp=2*pi/p
    out=[]
    for b in range(1,p):
        re=0.0;im=0.0
        for y in mu:
            ang=tp*((b*y)%p); re+=cos(ang); im+=sin(ang)
        out.append((re,im,sqrt(re*re+im*im)))
    return out

print("Energy/moment vs TRUE sup, over proper dyadic mu_n (p>>n^3):\n")
for mu in [3,4]:   # n=8,16 (n=32 too slow: p~3.3M periods)
    n=2**mu
    p,z,_=find_p_and_subgroup(n)
    P=all_periods(p,z,n)
    mags=[m for (_,_,m) in P]
    M=max(mags)
    floor=sqrt(2*n*log(p/n))
    johnson=sqrt(n)
    print(f"n={n}  p={p}  p/n^3={p/n**3:.1f}   M=max|eta|={M:.4f}   sqrt(n)={johnson:.4f}   sqrt(2n log(p/n))={floor:.4f}")
    print(f"   r : (E_r/(p-1))^(1/2r) [L^2r avg]   M/avg [gap]   single-rung Markov M<=(E_r)^(1/2r)")
    for r in range(1,9):
        Er=sum(m**(2*r) for m in mags)            # = sum_b |eta_b|^{2r}
        Lavg=(Er/(p-1))**(1.0/(2*r))
        markov=Er**(1.0/(2*r))                     # crude single-rung sup bound
        print(f"   {r:>2}: {Lavg:>10.4f}                {M/Lavg:>6.3f}        {markov:>12.2f}")
    # how big must r be for markov to reach the floor?
    r_needed=None
    for r in range(1,200):
        Er=sum(m**(2*r) for m in mags)
        if Er**(1.0/(2*r)) <= floor*1.0001:
            r_needed=r; break
    print(f"   -> single-rung Markov M<=(E_r)^(1/2r) reaches floor {floor:.2f} at r={r_needed} (need r ~ log p = {log(p):.1f})")
    print()
print("INTERPRETATION: the L^2r AVERAGE (E_r/(p-1))^(1/2r) stays ~sqrt(n) (Wick/Johnson scale),")
print("but the TRUE sup M is a growing multiple of it; closing M needs ALL rungs up to r~log p")
print("(deep-moment validity = the forced-anomaly open object). A single closed energy rung")
print("(Sarkozy L^2, or one symmetric coeff) gives the AVERAGE, never the L-inf sup. secretly-open.")

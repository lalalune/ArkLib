#!/usr/bin/env python3
"""
Lattice-walk / signed-basis moment structure at the boundary (#389 Fable wf2).

For n=2^m, the antipodal structure (Lam-Leung) says vanishing sums of n-th roots
decompose into +/- pairs.  So a vanishing 2r-term signed sum of n-th roots
sum_{i} eps_i zeta^{a_i} = 0  (eps in +/-1) corresponds, in the half-basis
Q(zeta_n) = Q-span of {zeta^0,...,zeta^{n/2-1}} (since zeta^{n/2}=-1), to a
CLOSED WALK on the lattice Z^{n/2} with steps +/- e_j.

The 2r-th additive moment  E_r(mu_n) = #{2r roots: a_1+...+a_r = a_{r+1}+...+a_{2r}}
= #{signed 2r-sums = 0}  over Q  =  W_r := #closed walks of length 2r on Z^{n/2}
(returning to origin), AS LONG AS p is large enough that no extra mod-p collisions.

Test:
 (W1) E_r(mu_n) over Q (= large p) equals the closed-walk count W_r(n/2) =
      coefficient extraction / the central moment of a sum of n/2 indep
      symmetric +/-1*(unit vector) steps -> exactly  prod / multinomial.
      Actually closed walks of length 2r on Z^d with +/- e_j steps:
      W_r(d) = sum over compositions ... = (2r)! [x^0...] (sum_j 2cos)...
      = constant term of (2 sum_j cos theta_j)^{2r} -- the moment of a random walk.
 (W2) the boundary energy threshold: E_r exceeds W_r exactly when p divides a
      walk-difference norm; tie the r-th moment threshold p > C_r(n) to r.
 (W3) Confirm E_2 = W_2 = 3d^2 - 3d ... wait that's 3(n/2)^2? check against 3n^2-3n.
"""
import sympy
from sympy import isprime
from collections import Counter
import itertools, math

def w_of_order(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def mu_n_list(p,n):
    w=w_of_order(p,n); return [pow(w,i,p) for i in range(n)]

def moment_r(p,n,r):
    """E_r = #{(a_1..a_2r) in mu^2r : sum first r = sum last r}."""
    G=mu_n_list(p,n)
    cnt=Counter()
    for combo in itertools.product(G,repeat=r):
        cnt[sum(combo)%p]+=1
    return sum(v*v for v in cnt.values())

def closed_walk_Z_halfdim(d, twor):
    """#closed walks length 2r on Z^d, steps in {+/- e_j : j<d}, NORMALIZED so that
       this counts ordered sequences of 2r steps summing to 0.
       = constant term of (sum_{j} (x_j + x_j^{-1}))^{2r}
       = sum over (k_1..k_d) with sum k_j = r of (2r)! / prod (k_j! k_j!).
       (each axis must be balanced)."""
    total=0
    # distribute r 'plus' picks ... actually: choose for each step which axis & sign.
    # net zero on each axis => equal +/- on each axis => 2*k_j steps on axis j, k_j each dir.
    # multinomial: (2r)!/prod((k_j)!(k_j)!) summed over k_1+..+k_d=r.
    for ks in _compositions(twor//2, d):
        num=math.factorial(twor)
        den=1
        for k in ks: den*=math.factorial(k)**2
        total+=num//den
    return total

def _compositions(total,parts):
    if parts==1: yield (total,); return
    for i in range(total+1):
        for rest in _compositions(total-i,parts-1):
            yield (i,)+rest

print("="*78)
print("PROBE 5: E_r(mu_n) (large p) vs closed-walk count W_r on Z^{n/2}")
print("Claim: E_r(mu_n) = (2r)! sum_{k_1+..+k_{n/2}=r} 1/prod(k_j!)^2  for p large")
print("="*78)
print(f"{'n':>3} {'r':>2} {'p':>7} {'E_r(mod p)':>12} {'W_r(Z^{n/2})':>14} {'match':>6}")
for n in (4,8,16):
    d=n//2
    # use a large p (char-0 proxy)
    p=n+1
    while not(isprime(p) and (p-1)%n==0 and p>10*n*n): p+=1
    for r in (1,2,3):
        if n>=16 and r>=3: continue  # too big to enumerate mu^3 for n=16? 16^3=4096 ok
        Er=moment_r(p,n,r)
        Wr=closed_walk_Z_halfdim(d,2*r)
        print(f"{n:>3} {r:>2} {p:>7} {Er:>12} {Wr:>14} {str(Er==Wr):>6}")
    print()

# RIGOROUS stress-test of the FLOOR pigeonhole.
# Claim: #floor-bad (config,prime) triples in window [4^s,8^s] << #primes in window.
# Equivalently: the floor-bad-prime SET (union over configs) is sparse relative to the window.
# We verify the KEY inequality components and the resultant HEIGHT bound at small s.
import math
from itertools import combinations
from sympy import primerange, factorint
# (1) Config count: antipodal-free size-2r configs in mu_s, r=rho*s+2
def n_configs(s, r):
    from math import comb
    return comb(s//2, 2*r) * (2**(2*r)) if 2*r <= s//2 else 0   # choose 2r of s/2 pairs, sign each
# (2) Resultant HEIGHT bound for the floor system {sum u=0, sum u^3=0}:
#     a spurious config's bad primes divide N(sum_{u in U} u) and N(sum u^3). |N| <= (2r)^{phi(s)}.
def height_bound_log2(s, r):
    phi = s//2  # phi(2^a)=2^{a-1}=s/2
    return phi * math.log2(2*r) if r>0 else 0
print("s   r   #configs(log2)   height|Res|(log2)   badprimes/cfg(window)   window#primes(log2)   pigeonhole?")
for (s,r,rho) in [(16,4,0.5),(32,8,0.5),(64,16,0.5),(128,32,0.5),(256,64,0.5),
                   (64,8,0.25),(128,16,0.25),(256,32,0.25)]:
    nc = n_configs(s,r)
    nc_log2 = math.log2(nc) if nc>0 else float('-inf')
    H = height_bound_log2(s,r)            # log2 |Res| bound per config
    # bad primes per config in window [4^s,8^s]: a number of log2-size H has <= H/(2s) prime factors >= 4^s
    bppc = H/(2*s) if s>0 else 0
    bad_triples_log2 = nc_log2 + math.log2(max(bppc,1e-9))
    win_log2 = 3*s - math.log2(s)         # log2(8^s/s) = 3s - log2 s
    ok = bad_triples_log2 < win_log2
    print(f"{s:4d} {r:3d}   {nc_log2:10.1f}      {H:10.1f}        {bppc:8.2f}            {win_log2:10.1f}        {'YES' if ok else 'NO -- FAILS'}  (bad_triples log2={bad_triples_log2:.1f})")
print()
print("Interpretation: pigeonhole holds iff bad_triples_log2 < window#primes_log2 (=3s-log2 s).")
print("Floor-good prime EXISTS in the window whenever YES. The construction may CHOOSE that prime.")

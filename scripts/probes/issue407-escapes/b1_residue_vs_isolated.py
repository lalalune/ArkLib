import numpy as np
import itertools

# CRITICAL adversarial test:
# The agent's "residue factor d" = Q_S / (expand g Cr) where C = expand g Cr is the LARGEST mu_g-coset core.
# Question A: Is deg(d) the SAME object as comment 142's "isolated count" (n-independent ~2k-1)?
# Question B: At the KAMBIRE WORST DIRECTION (d=gcd(a-b,n)>=2, BEYOND Johnson), 
#             what is deg(residue)? Comment 125 warns the binding family is LOW-exponent x^k = BGK.

# The agent's claim is that |S| - g*Cr.natDegree = d.natDegree, with C = expand F g Cr a SINGLE expand factor.
# But "largest mu_g-coset core" via ONE expand factor only captures cosets of a SINGLE granularity g.
# A general ragged set can be a UNION of cosets of DIFFERENT granularities + isolated points.
# So the agent's "residue d" is NOT the Beukers-Smyth isolated part (which removes ALL maximal coset families).
# Let's demonstrate: a set that is union of a mu_4 coset + a mu_2 coset + isolated.

n = 32
w = np.exp(2j*np.pi/n)
def coset(gen_pos, mult_pos_list):
    # coset gen * <w^mult>, return positions
    return set([(gen_pos + m) % n for m in mult_pos_list])

# mu_4 coset (positions step n/4=8): base 1, {1,9,17,25}
c4 = coset(1, [0,8,16,24])
# mu_2 coset (step n/2=16): base 3, {3,19}
c2 = coset(3, [0,16])
# isolated point: 5
iso = {5}
S = sorted(c4 | c2 | iso)
print("S positions:", S, "size", len(S))
roots = [w**p for p in S]
Q = np.poly(roots)
supp = [i for i,c in enumerate(Q[::-1]) if abs(c)>1e-7]
print("Q_S support:", supp)
# What's the largest SINGLE-granularity g with Q supported on multiples of g (i.e. expand g)?
def is_expand(supp, g):
    return all(s % g == 0 for s in supp)
maxg = 1
for g in range(2, n+1):
    if is_expand(supp, g):
        maxg = g
print("largest single-expand granularity g s.t. Q in range(expand g):", maxg)
# Since support has a gcd:
from math import gcd
from functools import reduce
gg = reduce(gcd, supp)
print("gcd of support =", gg, "(= the single expand granularity captured)")
# Agent's residue degree under THIS single-g peel:
deg_Q = len(S)
core_deg = gg * (deg_Q // gg) if gg>0 else 0  # = deg(C)= deg Q if fully expand; but if gg=1, core=0!
print("deg Q =", deg_Q, "; agent core deg (g*Cr.natDegree) = deg Q if monic single expand =", deg_Q if gg>1 else 0)
print("=> If gcd(support)=1, the single-expand 'core' is EMPTY, residue = ENTIRE S. Vacuous.")

import numpy as np
from math import gcd
from functools import reduce

# The agent's identity: Q_S = C * d, C = expand F g Cr (a g-sparse monic FACTOR), d the residue.
# Two readings:
#  (R1) C = the polynomial whose roots are the largest mu_g-coset-UNION SUBSET of S. 
#       Then C = prod_{x in core}(X - x), and C IS g-sparse (by factorization rigidity) IFF 
#       the core is genuinely a mu_g coset union. d = prod_{x in S\core}(X-x) = residue.
#       deg(d) = |S| - |core|.  <-- this is just |S| - core, ALREADY in ragged_excess_le_degree as 'c'.
#  (R2) C = any g-sparse monic factor of Q_S. 

# Under R1, the agent's "residue degree" = |S| - |largest coset core| = EXACTLY the quantity 
# 'S.card - cosetCore' already appearing as the LHS of ragged_excess_le_degree!
# So the "sharpening" replaces RHS (deg P - c) with deg(d) = |S| - |core| = the LHS itself.
# That is the IDENTITY |S| - c = |S| - c. It carries NO new bound. Let's confirm this reading is forced.

# Test: does Q_S even HAVE a g-sparse monic factor of degree = |core| for g>1, when core is a mu_g coset union?
# Core = mu_g coset {gamma * zeta^j}. prod_j (X - gamma zeta^j) = X^g - gamma^g (a binomial = expand g (X - gamma^g) with Cr = X - C(gamma^g)).
n=16
w=np.exp(2j*np.pi/n)
g=4  # mu_4 coset, step n/g = 4
gamma_pos=1
core_pos=[(gamma_pos + m*(n//g))%n for m in range(g)]  # {1,5,9,13}
print("mu_4 coset positions:", core_pos)
core_roots=[w**p for p in core_pos]
C=np.poly(core_roots)
print("core factor C coeffs (low->high):", [f"{c:.3f}" for c in C[::-1]])
# C should be X^4 - (w^1)^4 = X^4 - w^4
print("expand form: X^4 - gamma^g where gamma^g = w^4 =", w**4)
# So C = expand g (X - C(w^4)). deg C = g * deg(X-c) = g*1 = 4 = |core|. Good, R1 holds for a SINGLE coset.
# residue d = the rest. deg d = |S| - |core| = LHS of ragged_excess_le_degree.
print()
print("CONCLUSION: under the only sensible reading, deg(residue d) = |S| - |coset core|")
print("which is EXACTLY 'S.card - cosetCore', the LHS of ragged_excess_le_degree.")
print("The 'sharpening' replaces RHS=(deg P - c) by deg(d)=(|S|-c) = the LHS. It is the trivial identity LHS<=LHS.")

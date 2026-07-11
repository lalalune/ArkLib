import numpy as np
import itertools

# Test the agent's claim: degree-split of Q_S = (coset-core factor) * (ragged residue factor)
# Claim: |S| - deg(core) = deg(residue), and the residue degree is the "isolated/non-coset root count"
# Numeric (1): family Q = (X^m+1)*d(X), deg d < k, ragged-excess over antipodal core = k-1 EXACTLY
# Numeric (2): general realizable S can have residue degree EQUAL to k (so deg d < k is NOT unconditional)

# We just verify the algebra of the degree-split is trivially deg(Q) = deg(C)+deg(d), 
# which for monic factorization C*d means |S| = deg C + deg d. This is just deg multiplicativity.

# The REAL question: is "deg(residue d)" the same object comment 142 calls the "isolated count"?
# Comment 142: isolated count is n-INDEPENDENT (~2k-1, flat across n), via Schlickewei-Evertse.
# Agent's residue degree: claims it CAN equal k (their numeric 2: roots [0,5,10,13] support {0,1,3,4}).

# Let's check claim (2): roots at positions 0,5,10,13 in mu_16 (i.e. omega^0, omega^5, omega^10, omega^13)
n = 16
w = np.exp(2j*np.pi/n)
roots = [w**0, w**5, w**10, w**13]
# Q_S = prod (X - root)
Q = np.poly(roots)  # numpy poly: highest degree first
# support: which coeffs nonzero
supp = [n_idx for n_idx,c in enumerate(Q[::-1]) if abs(c) > 1e-9]
print("roots positions [0,5,10,13], Q_S coeffs (low->high):")
for idx,c in enumerate(Q[::-1]):
    if abs(c)>1e-9:
        print(f"  X^{idx}: {c:.4f}")
print("support:", supp)
# Largest coset core: is there a mu_g coset union inside? 
# {0,5,10,13}: differences. mu_g coset means closed under mult by g-th root of unity.
# Check antipodal pairing (g=2): x and -x. -1 = w^8. w^0*w^8=w^8 (not in set as position 8). 
# positions: 0,5,10,13. +8 mod 16: 8,13,2,5. So 5<->13 antipodal pair present (5+8=13). 0->8 absent, 10->2 absent.
# So largest g=2 coset core = {5,13} (size 2). residue = {0,10} -> but 0,10 differ by 10, +8=2 absent. 
print("antipodal pairs (x,-x):")
posset=set([0,5,10,13])
for p in [0,5,10,13]:
    print(f"  {p} <-> {(p+8)%16}", "PAIR" if (p+8)%16 in posset else "")

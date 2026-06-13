# Does #bad inject into the K-side count? K = 2^r C(n/2,r) = # antipodal-free r-subsets of mu_n (KKH26).
# The bad gamma = -e1(S) for (r+1)-subsets S in the deficit-2 band. Is there a natural injection
# {bad gamma} -> {antipodal-free r-subsets}? Test counts directly: K and #bad, and the ratio meaning.
import math
n=16
lad={3:97,4:145,5:89,6:113,7:225,8:104}
# antipodal-free r-subsets of mu_n: choose r of the n/2 antipodal classes, then a sign each: 2^r C(n/2,r) = K. yes.
for r in range(3,9):
    K=2**r*math.comb(8,r)
    print(f"r={r}: K(antipodal-free r-subsets)={K}, #bad={lad[r]}, K-#bad={K-lad[r]}, #bad/K={lad[r]/K:.4f}")
# The cleanest CLOSED candidate UPPER bound that is >= ladder and <= K:
# Candidate B1: #bad <= 2^{r-1} C(n/2, r-1) * (n/2) / something... try simple closed forms <=K, >=ladder.
print()
print("Closed-form candidate tests (must be >= #bad AND <= K for all r,n):")
# B1: n * C(n/2-1, r-1)  (size of e1-image if e1 ranged over 'one rep per antipodal class times shifts')
for r in range(3,9):
    K=2**r*math.comb(8,r)
    b1 = n*math.comb(8-1, r-1)
    b2 = 2**(r-1)*math.comb(8,r-1) + 1   # half-K-shifted
    b3 = math.comb(n, r+1)               # trivial choose (the in-tree clean bound)
    print(f"r={r}: #bad={lad[r]:>3}  K={K:>5}  | n*C(7,r-1)={b1:>4} | 2^(r-1)C(8,r-1)+1={b2:>5} | C(16,r+1)={b3:>5}")

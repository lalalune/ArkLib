import numpy as np
from itertools import combinations
from math import comb
# CLAIM: #{all-antipodal e2=0 subsets of mu_n with j=2i pairs} = C(n/4, i).
# (S = union of i antipodal-pair-classes of mu_{n/2}-squares summing to zero = i-subset of n/4 pair-classes.)
def all_antipodal_e2zero(n, j):
    # antipodal pairs of mu_n: {k, k+n/2} for k in 0..n/2-1. choose j of them, check e2=0 (sum of squares=0)
    R=[np.exp(2j*np.pi*k/n) for k in range(n)]
    half=n//2
    cnt=0
    for pairs in combinations(range(half), j):
        S=list(pairs)+[k+half for k in pairs]
        p2=sum(R[k]**2 for k in S)
        e1=sum(R[k] for k in S)  # =0 always for antipodal
        if abs(p2)<1e-7:  # e2 = -p2/2 = 0
            cnt+=1
    return cnt
print("all-antipodal e2=0 count at j pairs  vs  C(n/4, j/2) [0 if j odd]")
print(f"{'n':>4} {'j':>3} {'measured':>9} {'C(n/4,j/2)':>11} {'match':>6}")
for n in [8,16,32,64]:
    nq=n//4
    for j in range(1, min(n//2,8)+1):
        if comb(n//2, j) > 3_000_000: break
        m=all_antipodal_e2zero(n,j)
        pred = comb(nq, j//2) if j%2==0 else 0
        print(f"{n:>4} {j:>3} {m:>9} {pred:>11} {'OK' if m==pred else 'X':>6}")
    print()

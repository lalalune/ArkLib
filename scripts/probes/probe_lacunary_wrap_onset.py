import math
# Onset prediction from _CyclotomicLatticeWrapOnset: r* ~ (1/2) lambda_1^{l1}(p0) ~ (1/2) p^{2/n}
# (d=n/2, lattice index p, l1 shortest vector ~ p^{1/d}=p^{2/n}).
# At beta=4: p ~ n^4, so p^{2/n} = n^{8/n}.
for n in [16,32,64,256,1024,2**20,2**30]:
    p_2n = n**(8.0/n)  # n^{2*beta/n} with beta=4
    rstar = 0.5*p_2n
    needed = 4*math.log(n)  # r ~ log p = beta log n = 4 log n
    print(f"n={n:>10}: p^(2/n)=n^(8/n)={p_2n:8.3f}  r*~{rstar:7.3f}  needed r~log p={needed:7.2f}  wrap-onset {'BEFORE' if rstar<needed else 'AFTER'} needed")
print()
print("INTERPRETATION: at beta=4 the lattice l1-shortest-vector p^{2/n} -> 1 as n grows (since 8/n -> 0),")
print("so onset r* -> 1/2: wraparound turns on IMMEDIATELY (r>=1) for large n. The wrap excess is present")
print("at ALL needed depths for the prize n=2^30. The route can NOT rely on Q4=0.")
print("=> Must bound E_r^char-p DIRECTLY (with wrap), not via char-0 + Q4=0.")

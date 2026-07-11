"""
RH-transfer attack: is the prize TRUE under GRH? The good-prime question: does a prime p in [N,2N],
N~2^38 n^4, exist that is GOOD (E_r(F_p)<=Wick for all r<=log p)? Bad primes p divide some cyclotomic
norm Res. Under GRH, effective Chebotarev (Lagarias-Odlyzko) controls prime splitting. The decisive
quantity: #bad primes in [N,2N] vs the prime count ~N/log N. If #bad << N/log N, a good prime EXISTS.
Estimate #bad via: bad primes for depth<=R are divisors of R_n(R)=prod of nonzero cyclotomic-norm
differences; #distinct bad = omega(R_n(R)) <= log R_n. Compute log R_n(R) and compare to log(prime density).
"""
import math
# At depth R, the distinct short differences delta=Sum x - Sum y (|delta|_arch <= 2R per conjugate),
# count ~ (subset-sum spectrum size) <= C(n,<=R)-ish, each |N(delta)| <= (2R)^{n/2}.
# log R_n(R) <= (#distinct delta) * (n/2) * log(2R).
def log_bad_count(n, R):
    # #distinct delta at depth R: bounded by the r-fold sumset size ~ min(p, n^{2R}) but the DISTINCT
    # cyclotomic-norm values is much smaller; use the subset-sum spectrum |Sigma_R| ~ (R-fold). Use a
    # generous bound: #distinct ~ (2R)^? ; we use the rigorous |N(delta)|<=(2R)^{n/2} and #delta <= n^{2R}.
    num_delta = min(2**(n), (2*R)**(n))   # crude upper bound on distinct differences (huge)
    log_each_norm = (n/2)*math.log(2*R)   # log|N(delta)|
    # omega(R_n) <= sum of omega(N(delta)) <= #delta * log_each_norm / log 2 (each norm has <= log2 factors)
    return math.log(num_delta) + math.log(log_each_norm/math.log(2) + 1)
print("GRH-transfer feasibility: #bad primes (log) vs prize-scale prime supply (log N).")
print(f"{'n':>6} {'R=log p':>8} {'log #bad (crude)':>16} {'log N (N=2^38 n^4)':>18} {'good prime?':>11}")
for mu in (4,5,8,16,30):
    n=2**mu
    N=2**38 * n**4
    logN=math.log(N)
    R=int(logN)  # depth ~ log p
    # the RIGOROUS bad count: only depths where wraparound is possible AND the prize prime could be bad.
    # KEY: |N(delta)| <= (2R)^{n/2}; for p > (2R)^{n/2} ALL primes are good at depth R (norm bound).
    # So bad primes at depth R only exist if p <= (2R)^{n/2}. Compare prize p=N to (2R)^{n/2}:
    log_normbound = (n/2)*math.log(2*R)
    safe = logN > log_normbound  # if prize prime EXCEEDS the norm bound, it's GUARANTEED good at depth R
    print(f"{n:>6} {R:>8} {'n/2 log(2R)='+f'{log_normbound:.0f}':>16} {logN:>18.0f} {'GUARANTEED GOOD' if safe else 'norm-bound vacuous':>11}")
print()
print("THE DECISIVE CHECK: is the prize prime p~2^38 n^4 ABOVE the norm bound (2R)^{n/2} at depth R=log p?")
print("If logN > (n/2)log(2R), then p>(2R)^{n/2} => NO wraparound at depth R => GOOD unconditionally (no GRH needed!).")

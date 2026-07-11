"""
The decisive reframing: GRH-transfer works iff the NUMBER of bad primes in [N,2N] is < the prime count
~N/log N, regardless of how LARGE individual bad primes can be. A prime p in [N,2N] is bad iff it divides
SOME nonzero cyclotomic-norm difference of bounded depth. #bad <= omega(prod of relevant norms). But the
norms only have boundedly many prime factors in [N,2N]: a norm of size (2R)^{n/2} has <= log((2R)^{n/2})/log N
prime factors that large. So #bad-in-[N,2N] per delta <= (n/2)log(2R)/log N. Times #distinct delta.
Estimate whether sum < N/log N.
"""
import math
print("GRH-transfer DECISIVE: #bad primes IN [N,2N] vs prime supply N/log N (N=2^38 n^4, depth R=log N):")
print(f"{'n':>8} {'logN':>6} {'#delta(log)':>11} {'bad/delta in[N,2N]':>18} {'log #bad':>9} {'log supply':>11} {'good?':>6}")
for mu in (8,16,30):
    n=2**mu
    N=2.0**38 * n**4
    logN=math.log(N); R=int(logN)
    # #distinct delta (cyclotomic differences) at depth R: bounded by subset-sum spectrum.
    # rigorous-ish: the distinct values of Sum_{i<=R} x_i in Z[zeta_n] <= (R+1)^{n} (each coord bounded) -- huge.
    # BUT we only need delta with |N(delta)| having a prime factor in [N,2N]. 
    log_num_delta = min(n*math.log(2), 2*R*math.log(n))   # log #distinct delta (generous)
    # per delta: #prime-factors-in-[N,2N] of N(delta) <= log|N(delta)| / log N = (n/2 log 2R)/logN
    bad_per_delta = (n/2)*math.log(2*R)/logN
    log_bad = log_num_delta + math.log(max(bad_per_delta,1e-9))
    log_supply = logN - math.log(logN)  # log(N/log N)
    good = log_bad < log_supply
    print(f"{n:>8} {logN:>6.0f} {log_num_delta:>11.1f} {bad_per_delta:>18.2e} {log_bad:>9.1f} {log_supply:>11.1f} {str(good):>6}")
print()
print("READING: if log #bad < log supply, a good prime EXISTS in [N,2N] => prize TRUE (the count argument).")
print("The binding quantity is log #distinct delta (the subset-sum spectrum). If it's polynomial in log N,")
print("the count wins. If exponential in n, it loses. THIS is the precise open quantity = BCHKS subset-sum.")

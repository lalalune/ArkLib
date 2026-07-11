# CORRECTED pigeonhole: floor bad primes divide ONE integer D (height <= n^{n/2}), so
# #distinct bad primes <= log2 D <= (n/2) log2 n -- poly(n), NOT exp. Compare to window primes.
import math
print("n=2^mu  | #bad primes <= log2 D ~ (n/2)log2 n | window primes ~1 mod n in [n^4,n^6] ~ n^3/ln | bad<<window?")
for mu in [10,20,30,40]:
    n = 2**mu
    # log2 D: D height <= (n^2+n)^{n/2} (proven e2-rigidity species); log2 = (n/2)*log2(n^2+n) ~ (n/2)*2mu = n*mu
    log2_D = (n/2)*math.log2(n*n+n)
    nbad = log2_D            # #distinct prime factors of D <= log2 D
    # window [n^4,n^6], primes ===1 mod n ~ (n^6 - n^4)/(n * ln(n^6))  (Dirichlet, density 1/phi(n)~1/n)
    win_primes_log2 = 6*mu - mu - math.log2(6*mu)   # log2( n^6 / (n * ln) ) approx = 5mu - log2(6 mu)
    nbad_log2 = math.log2(nbad)
    print(f"2^{mu:2d}   | {nbad_log2:8.1f} (log2)              | {win_primes_log2:8.1f} (log2)                       | {'YES' if nbad_log2 < win_primes_log2 else 'NO'}")
print()
print("KEY: #bad primes ~ 2^{log2((n/2)log2 D)} = poly-log in the EXPONENT -> nbad_log2 ~ log2(n mu) = mu+log mu;")
print("     window primes_log2 ~ 5 mu.  So nbad_log2 (~mu) << window (~5mu): a good prime EXISTS. Robust.")

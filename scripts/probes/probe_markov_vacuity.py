import sympy, math

# Prize regime: thin 2-power subgroup mu_n in F_p^*, n=2^a, p = k*n+1, beta~4 => p ~ n^4, m=(p-1)/n ~ n^3
# Wraparound W_r(p) at depth r. Total (alpha, bad-prime) incidence over all admissible primes:
#   Sum_relations omega(N(alpha)) <= n^{2r} * phi(n) * log2(2r)  (per-relation bound, archimedean)
# Markov: #{p admissible : W_r(p) >= T} <= TotalIncidence / T.
# VACUOUS when RHS >= number of admissible primes pi_adm, i.e. T <= TotalIncidence/pi_adm = AVERAGE wraparound.

def admissible_primes(n, beta, count=30):
    target = int(n**beta)
    ps = []
    k = max(1, target // n)
    while len(ps) < count and k < 50 * target // n + 100000:
        p = k * n + 1
        if sympy.isprime(p):
            ps.append(p)
        k += 1
    return ps

for a in range(3, 7):
    n = 2 ** a
    beta = 4.0
    r = 2
    ps = admissible_primes(n, beta, count=30)
    if not ps:
        continue
    phi_n = n // 2
    log2_2r = math.log2(2 * r)
    total_incidence = (n ** (2 * r)) * phi_n * log2_2r
    pi_adm = len(ps)
    avg_W = total_incidence / pi_adm
    p = ps[len(ps) // 2]
    Wprize = n * math.log(p / n)
    vacuous = Wprize <= avg_W
    print("n=%4d p~%10d  #rel=n^%d=%12d  avgW=%.3e  Wprize=%.3e  Markov-vacuous? %s" %
          (n, p, 2 * r, n ** (2 * r), avg_W, Wprize, vacuous))

# PROBE: how far is the PROVEN r=2 Sidon bound M <= (3q)^{1/4} sqrt(n) from the
# frame's OPEN target NearRamanujanSqrtLog  M <= C sqrt(n log(q/n)) ?
# i.e. what constant C does r=2 force, and does it blow up in the prize regime (thin mu_n, q=n^beta)?
# Probe-first on EXACT thin mu_n=<g^((p-1)/n)>, n=2^a, p>>n^3, NEVER n=q-1.
import sympy, math, cmath

def thin_subgroup_max_period(p, n):
    # mu_n = unique order-n subgroup of F_p^*. Need n | p-1, (p-1)/n >= 2 (proper).
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)               # generator of mu_n
    mu = [pow(h, j, p) for j in range(n)]
    zeta = cmath.exp(2j*cmath.pi/p)
    best = 0.0
    for b in range(1, p):
        s = sum(zeta**((b*x) % p) for x in mu)
        best = max(best, abs(s))
    return best

# prize-ish small instances (exact, proper, p >> n^3, multiple primes incl Fermat 257)
cases = []
for n in [4, 8, 16]:
    # find primes p ≡ 1 mod n with p > n^3 and (p-1)/n >= 2
    cnt = 0
    p = max(n*n*n, n)+1
    while cnt < 3:
        if sympy.isprime(p) and (p-1) % n == 0 and (p-1)//n >= 2:
            cases.append((p, n)); cnt += 1
        p += 1
cases.append((257, 16))  # Fermat 257, n=16 proper (256/16=16)

print(f"{'p':>8} {'n':>4} {'beta':>6} {'M':>9} {'(3q)^.25 sqrt n':>16} {'sqrt(n log(q/n))':>17} {'C_forced':>9} {'C_true=M/that':>13}")
for (p, n) in cases:
    M = thin_subgroup_max_period(p, n)
    q = p
    beta = math.log(q)/math.log(n)
    sidon_bound = (3*q)**0.25 * math.sqrt(n)          # proven r=2 upper bound
    nearram_scale = math.sqrt(n * math.log(q/n))      # frame target shape
    C_forced = sidon_bound / nearram_scale            # C that r=2 gives for NearRamanujanSqrtLog
    C_true = M / nearram_scale                         # the ACTUAL constant M needs (the real answer)
    print(f"{p:>8} {n:>4} {beta:>6.2f} {M:>9.3f} {sidon_bound:>16.3f} {nearram_scale:>17.3f} {C_forced:>9.3f} {C_true:>13.3f}")
print()
print("READING: C_forced is the constant the PROVEN r=2 bound certifies for the frame's open hypothesis.")
print("If C_forced grows with q (prize regime q=n^beta, beta>=4), r=2 does NOT discharge the frame.")
print("C_true (= M / sqrt(n log(q/n))) is the actual absolute constant the prize claims is O(1).")

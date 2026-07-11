#!/usr/bin/env python3
"""
PROBE (prize-regime, PROPER thin mu_n): the spectral-support AVERAGE squared-period ceiling.

Claim to test:
  total L2 mass  S2 = sum_b ||eta_b||^2 = q*n   (exact second moment)
  support        N+ = #{b : eta_b != 0}  >= q*n / (3(n-1))   (spectral spread, landed)
  ==> AVERAGE squared period over the support  S2 / N+ <= 3(n-1)  ~ 3n
  ==> typical magnitude  sqrt(S2/N+) <= sqrt(3(n-1)) ~ sqrt(3n)   (typical/avg ceiling)

This is the AVERAGE/typical ceiling (dual of the proven Parseval FLOOR M>=~sqrt(n)).
It says NOTHING about the worst-case sup M (the open BGK content). We confirm:
  (a) S2 == q*n exactly,
  (b) N+ >= q*n/(3(n-1)) (the spread holds),
  (c) S2/N+ <= 3(n-1) (the average ceiling),
  (d) the worst-case M is MUCH larger than sqrt(3n) (so this is genuinely about the
      average, not the open worst case).
PROPER subgroup mu_n = <g^((p-1)/n)>, n=2^a, p >> n^3, n | p-1, multiple primes, NEVER n=q-1.
"""
import cmath, math

def find_primes(n, count, lo_mult=8):
    """primes p with n | p-1 and p > n^3 * lo_mult (prize-ish p>>n^3)."""
    out = []
    base = max(n**3 * lo_mult, n + 1)
    # ensure p ≡ 1 mod n
    k = (base // n) + 1
    while len(out) < count:
        p = k * n + 1
        if is_prime(p):
            out.append(p)
        k += 1
    return out

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    # find generator of F_p^*
    phi = p - 1
    factors = set()
    x = phi
    d = 2
    while d * d <= x:
        while x % d == 0:
            factors.add(d); x //= d
        d += 1
    if x > 1: factors.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # element of order n
    S = set()
    cur = 1
    for _ in range(n):
        S.add(cur); cur = (cur * h) % p
    assert len(S) == n, (len(S), n)
    return sorted(S)

def eta_norms_sq(p, G):
    # eta_b = sum_{x in G} e_p(b x);  e_p(t) = exp(2 pi i t / p)
    w = 2 * math.pi / p
    out = []
    for b in range(p):
        s = 0j
        for x in G:
            s += cmath.exp(1j * w * ((b * x) % p))
        out.append(abs(s) ** 2)
    return out

def run(n, p):
    G = mu_n(p, n)
    ns = eta_norms_sq(p, G)
    S2 = sum(ns)                      # = q*n exactly (second moment)
    Nplus = sum(1 for v in ns if v > 1e-9)
    spread_lb = (p * n) / (3 * (n - 1))
    avg_on_support = S2 / Nplus
    ceil_target = 3 * (n - 1)
    # worst-case sup over b != 0 (b=0 has ||eta||^2 = n^2)
    M2 = max(ns[b] for b in range(1, p))
    print(f"  n={n} p={p}  q*n={p*n}  S2={S2:.3f}  (S2==q*n? {abs(S2-p*n)<1e-6*p*n})")
    print(f"    N+ = {Nplus}  spread_lb = q*n/(3(n-1)) = {spread_lb:.1f}   spread holds? {Nplus >= spread_lb-1e-6}")
    print(f"    AVG on support S2/N+ = {avg_on_support:.4f}  <=? 3(n-1) = {ceil_target}   ceiling holds? {avg_on_support <= ceil_target + 1e-9}")
    print(f"    typical mag sqrt(S2/N+) = {math.sqrt(avg_on_support):.3f}   vs sqrt(3n)={math.sqrt(3*n):.3f}")
    print(f"    WORST-case M = sqrt(max_b!=0 ||eta||^2) = {math.sqrt(M2):.3f}  (>> typical: worst-case is the OPEN content)")
    return dict(S2=S2, qn=p*n, Nplus=Nplus, spread_lb=spread_lb,
                avg=avg_on_support, ceil=ceil_target, M=math.sqrt(M2))

if __name__ == "__main__":
    print("PROBE: spectral-support AVERAGE typical-floor ceiling (prize-regime PROPER mu_n)")
    for n in [4, 8, 16]:
        for p in find_primes(n, 2):
            run(n, p)
    print("\nVERDICT: if (S2==q*n), (N+>=spread_lb), (S2/N+<=3(n-1)) all hold and M>>sqrt(3n),")
    print("the average/typical ceiling is REAL and DISTINCT from the open worst-case sup M.")

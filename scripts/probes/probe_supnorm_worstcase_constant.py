#!/usr/bin/env python3
# PROPOSE-AND-REFUTE: pin the worst-case constant C in  M(n,p) <= C*sqrt(n*ln m),
# m = (p-1)/n the index.  Conjecture R<=sqrt(2) is already refuted (R=1.484 seen).
# Here we HUNT the sup of R over a wide grid (every prime p=n*m+1 in range, many m per n,
# plus small n exhaustively) to find the true empirical worst case and where it lives.
# Also tests the alternative normalizations to see which is tightest (closed-form candidate).
import sympy, cmath, math

def musub(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)], g

def supnorm(n, p):
    G, g = musub(n, p)
    m = (p - 1) // n
    w = 2 * math.pi / p
    mx = 0.0
    rep = 1
    for c in range(m):
        s = 0j
        for x in G:
            s += cmath.exp(1j * w * ((rep * x) % p))
        a = abs(s)
        if a > mx:
            mx = a
        rep = (rep * g) % p
    return mx

# Hunt: for each n (power of 2), scan ALL primes p=n*m+1 with m in [m_lo, m_hi].
worst = (0.0, None)
worst_loglog = (0.0, None)
print(f"{'n':>5}{'p':>9}{'m':>7}{'M':>8}{'M/sqrtn':>9}{'R=M/sqrt(n ln m)':>18}{'M/sqrt(n ln(2m))':>18}")
for mu in range(2, 11):
    n = 2 ** mu
    cnt = 0
    bestR_thisn = (0.0, None)
    m = 2
    while n * m + 1 < min(700000, 60000 + n * 200) and cnt < 60:
        p = n * m + 1
        if sympy.isprime(p):
            M = supnorm(n, p)
            R = M / math.sqrt(n * math.log(m)) if m >= 2 else 0
            R2 = M / math.sqrt(n * math.log(2 * m))
            if R > bestR_thisn[0]:
                bestR_thisn = (R, (n, p, m, M, R, R2))
            if R > worst[0]:
                worst = (R, (n, p, m, M))
            if R2 > worst_loglog[0]:
                worst_loglog = (R2, (n, p, m, M))
            cnt += 1
        m += 1
    if bestR_thisn[1]:
        n_, p_, m_, M_, R_, R2_ = bestR_thisn[1]
        print(f"{n_:>5}{p_:>9}{m_:>7}{M_:>8.2f}{M_/math.sqrt(n_):>9.3f}{R_:>18.4f}{R2_:>18.4f}")

print()
print(f"WORST R = M/sqrt(n ln m):       {worst[0]:.4f}  at (n,p,m,M)={worst[1]}")
print(f"WORST R2= M/sqrt(n ln(2m)):     {worst_loglog[0]:.4f}  at (n,p,m,M)={worst_loglog[1][:3] if worst_loglog[1] else None}")
print()
print("Interpretation: if R stays bounded by a fixed C across this hunt, the closed-form")
print("  delta* = 1 - rho - H(rho)/(beta log2 n)  has the RIGHT shape with constant <= C^2-ish.")
print("  The sqrt(2) conjecture is refuted iff WORST R > 1.4142.")

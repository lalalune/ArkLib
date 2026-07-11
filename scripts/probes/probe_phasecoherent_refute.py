#!/usr/bin/env python3
# Probe: PhaseCoherentUniform refutation via Parseval second moment.
# If every b!=0 had ||eta_b|| = ((m-1)sqrt(q)+1)/m  [the triangle-saturation value],
# then sum_{b!=0} ||eta_b||^2 would FAR exceed the true Parseval value qn - n^2.
import cmath, math


def eta(b, mu, p):
    return sum(cmath.exp(2j * math.pi * (b * y % p) / p) for y in mu)


def find_prime_and_mu(n):
    k = max(2, n * n + 2)
    while True:
        p = k * n + 1
        if all(p % i for i in range(2, int(p ** 0.5) + 1)):
            g = 2
            while g < p:
                h = pow(g, (p - 1) // n, p)
                if pow(h, n, p) == 1:
                    ok = all(pow(h, n // dv, p) != 1
                             for dv in range(2, n + 1) if n % dv == 0)
                    if ok:
                        mu = sorted({pow(h, j, p) for j in range(n)})
                        if len(mu) == n:
                            return p, mu
                g += 1
        k += 1


for n in [8, 16, 32]:
    p, mu = find_prime_and_mu(n)
    d = n
    m = (p - 1) // d
    sat = ((m - 1) * math.sqrt(p) + 1) / m
    true_sum_nonzero = p * n - n * n
    claimed_sum_nonzero = (p - 1) * sat ** 2
    Mmeas = max(abs(eta(b, mu, p)) for b in range(1, min(p, 4000)))
    print("n=%d p=%d m=%d" % (n, p, m))
    print("  sat=%.2f  sqrt(q)=%.2f  sqrt(n)=%.2f" % (sat, math.sqrt(p), math.sqrt(n)))
    print("  true   sum_(b!=0) ||eta||^2 = qn-n^2 = %d" % true_sum_nonzero)
    print("  CLAIMED (if coherent) = (q-1)*sat^2 = %.3e" % claimed_sum_nonzero)
    print("  ratio claimed/true = %.2f  (>>1 => CONTRADICTION)" %
          (claimed_sum_nonzero / true_sum_nonzero))
    print("  measured M (partial) = %.2f  vs sat %.2f (M << sat expected)" % (Mmeas, sat))

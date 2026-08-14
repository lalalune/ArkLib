#!/usr/bin/env python3
"""
VALIDATE the power-of-2 sparse floor law over REAL finite fields F_p,
PROPER subgroups mu_n (m=(p-1)/n>1), p==1 mod n, p>>n^3, NEVER n=q-1.

Closed form claim: for support t=2^s, the witness
  W_s(X) = prod_{j=mu-s+1}^{mu} Phi_{2^j}(X) = (X^n-1)/(X^{n/2^s}-1)
has support t=2^s and EXACTLY (1-1/2^s)*n = n - n/2^s roots in mu_n.

Proof sketch to verify: (X^n-1)/(X^{n/2^s}-1) vanishes on mu_n \ mu_{n/2^s},
which has size n - n/2^s. Support of (X^n-1)/(X^{d}-1) = X^{n-d}+X^{n-2d}+...+1
has exactly n/d = 2^s terms.  <-- KEY: it's the cyclotomic SUM 1+Y+...+Y^{2^s-1}
with Y=X^{n/2^s}. So support = 2^s EXACTLY. roots = mu_n minus the Y=1 fiber.
"""

def find_prime(n, want_bits=60):
    # p == 1 mod n, p large (>> n^3), prime
    import sympy as sp
    base = max(n**3 * 1000, 2**want_bits)
    k = base // n + 1
    while True:
        p = k * n + 1
        if sp.isprime(p):
            return p
        k += 1


def roots_in_mu_n(p, n, exps):
    """exps: list of exponents with coeff 1 (the sparse poly sum X^e). Count roots in mu_n."""
    g = primitive_root(p)
    # generator of mu_n: h = g^((p-1)/n)
    h = pow(g, (p - 1) // n, p)
    cnt = 0
    for j in range(n):
        x = pow(h, j, p)
        val = sum(pow(x, e, p) for e in exps) % p
        if val == 0:
            cnt += 1
    return cnt


def primitive_root(p):
    import sympy as sp
    return int(sp.primitive_root(p))


def witness_exps(n, s):
    # W_s = sum_{i=0}^{2^s-1} X^{i*(n/2^s)}  = (X^n-1)/(X^{n/2^s}-1)
    d = n // (2 ** s)
    return [i * d for i in range(2 ** s)]


print("FF validation of power-of-2 sparse floor: t=2^s -> n-n/2^s roots")
print("=" * 70)
import sympy as sp
for mu in range(3, 7):
    n = 2 ** mu
    p = find_prime(n)
    m = (p - 1) // n
    print("\n--- n=%d, p=%d (m=(p-1)/n=%d, p/n^3=%.1f) ---" % (n, p, m, p / n**3))
    for s in range(1, mu + 1):
        exps = witness_exps(n, s)
        t = len(exps)
        rc = roots_in_mu_n(p, n, exps)
        pred = n - n // (2 ** s)
        ok = "OK" if rc == pred else "*** MISMATCH ***"
        print("  s=%d t=2^%d=%2d: roots=%3d  pred=n-n/%d=%3d  %s" %
              (s, s, t, rc, 2**s, pred, ok))

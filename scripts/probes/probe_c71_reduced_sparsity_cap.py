"""PROBE: does the m-sparse mu_n-incidence drop to (#distinct reduced exps) - 1?

After mod-n reduction, the direction gbar has m' = #distinct nonzero-coef residues terms.
Claim: deg gcd(X^n-1, gbar) <= m' - 1 ?  (the sparsity-incidence cap, MUCH sharper than < n
for small m).  Tested against exact GF(p)[X] gcd.  rule-2: PROPER thin mu_n=2^a, p==1 mod n
incl p>n^3 + Fermat, NEVER n=q-1, wrap-around supports.

(If this FAILS it is a useful refutation; if it HOLDS it is a genuine sharp cap to formalize.)
"""
from sympy import symbols, Poly, GF, gcd
import random

X = symbols('X')


def is_prime(x):
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def deg_gcd(coefs, n, p):
    dom = GF(p)
    gpoly = Poly(sum(c * X**e for e, c in coefs.items()), X, domain=dom)
    cyc = Poly(X**n - 1, X, domain=dom)
    return gcd(cyc, gpoly).degree()


def reduce_mod_n(coefs, n, p):
    r = {}
    for e, c in coefs.items():
        e2 = e % n
        r[e2] = (r.get(e2, 0) + c) % p
    return {e: c for e, c in r.items() if c % p != 0}


def primes_for(n):
    ps = [pp for pp in range(n + 1, 70000) if pp % n == 1 and is_prime(pp)]
    chosen = [ps[0]]
    big = [pp for pp in ps if pp > n**3]
    if big:
        chosen.append(big[0])
    for f in (257, 65537):
        if f % n == 1 and f not in chosen:
            chosen.append(f)
            break
    return chosen


def run():
    random.seed(23)
    cases = capOK = 0
    bad = []
    for a in (2, 3, 4):
        n = 2**a
        for p in primes_for(n):
            for m in (2, 3, 4, 5):
                for _ in range(60):
                    exps = sorted(random.sample(range(0, 3 * n), m))
                    coefs = {e: random.randrange(1, p) for e in exps}
                    gbar = reduce_mod_n(coefs, n, p)
                    if not gbar:
                        continue
                    mprime = len(gbar)
                    d = deg_gcd(gbar, n, p)
                    cases += 1
                    if d <= mprime - 1:
                        capOK += 1
                    else:
                        bad.append((n, p, exps, d, mprime))
    print("cases=%d" % cases)
    print("sparsity cap deg gcd(gbar) <= (#distinct reduced exps) - 1: %d/%d" % (capOK, cases))
    if bad:
        print("VIOLATIONS (d > m'-1):", bad[:8])
    else:
        print("NO violations -- sparsity cap HOLDS.")


run()

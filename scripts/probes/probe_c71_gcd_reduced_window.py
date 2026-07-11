"""PROBE: thinness-essential reduced-window bound on deg gcd(X^n - 1, g) over mu_n.

Over mu_n every x satisfies x^n = 1, so x^e = x^(e mod n). The direction polynomial g
restricted to mu_n agrees with gbar = sum_e c_e X^(e mod n) (deg < n, same-residue terms
collapsed). Hence the mu_n-incidence count equals deg gcd(X^n - 1, gbar).

Claims tested (rule 2: PROPER thin mu_n = 2^a, prime p == 1 mod n incl p > n^3 + Fermat,
NEVER n = q-1, multi-prime). All gcds computed exactly in GF(p)[X] via sympy.

  A (reduction):   deg gcd(X^n-1, g) == deg gcd(X^n-1, gbar)            [thinness-essential]
  B (window):      deg gcd(X^n-1, gbar) <= rtop - rbot of gbar support  [explicit usable bound]
  C (wrap helps):  reduced window < raw window when support wraps past n
"""
from sympy import symbols, Poly, GF, gcd

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
    import random
    random.seed(11)
    cases = redEq = winOK = wrapHelps = 0
    bad = []
    for a in (2, 3, 4):
        n = 2**a
        for p in primes_for(n):
            for m in (3, 4, 5):
                for _ in range(40):
                    exps = sorted(random.sample(range(0, 3 * n), m))
                    coefs = {e: random.randrange(1, p) for e in exps}
                    gbar = reduce_mod_n(coefs, n, p)
                    if not gbar:
                        continue
                    rexps = sorted(gbar.keys())
                    rwin = rexps[-1] - rexps[0]
                    rawwin = exps[-1] - exps[0]
                    d_raw = deg_gcd(coefs, n, p)
                    d_red = deg_gcd(gbar, n, p)
                    cases += 1
                    if d_raw == d_red:
                        redEq += 1
                    else:
                        bad.append(('RED', n, p, exps, d_raw, d_red))
                    if d_red <= rwin:
                        winOK += 1
                    else:
                        bad.append(('WIN', n, p, exps, d_red, rwin))
                    if rwin < rawwin:
                        wrapHelps += 1
    print("cases=%d" % cases)
    print("A reduction deg gcd(g)==deg gcd(gbar): %d/%d" % (redEq, cases))
    print("B reduced-window deg gcd(gbar)<=rtop-rbot: %d/%d" % (winOK, cases))
    print("C reduced window < raw window (wrap helps): %d/%d" % (wrapHelps, cases))
    if bad:
        print("VIOLATIONS:", bad[:5])
    else:
        print("NO violations.")


run()

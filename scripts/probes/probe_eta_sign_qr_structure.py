#!/usr/bin/env python3
"""UNCONTESTED LANE: the SIGN s_b in {+1,-1} of the REAL period eta_b (proven real on neg-closed mu_n).
etareal pinned arg(eta_b) in {0,pi} => eta_b = s_b * |eta_b|, s_b in {+1,-1}. The OPEN object
(etareal next-lane): is the sign pattern s_b self-similar / Legendre-structured / a character?

PROBE-FIRST (rule 2): proper thin mu_n=2^a, p>>n^3, p=1 mod n, NEVER n=q-1, multiple primes incl Fermat-type.
We test concrete sign-law candidates that would be NEW structure (NOT the b* magnitude-alignment wall wf-A1 mapped):
  H1: s_b depends ONLY on the coset b*mu_n (well-defined on F_p^*/mu_n)?
  H2: s_b = Legendre(b | p)?  (sign = quadratic character)
  H3: s_b multiplicative on the quotient: s_{b1 b2} = s_{b1} s_{b2}?  (is b->s_b a CHARACTER?)
  H4: dilation law: s_{zeta b}/s_b (zeta order 2n) -- constant over b? (the N13 relative sign)
Honesty: report counts, NO overclaim. A clean character/Legendre law = NEW frequency-AWARE structure
(survives the meta-theorem, which kills frequency-BLIND methods). A no-structure verdict = a rule-4 wall.
"""
import numpy as np
import sympy


def gen(p):
    fac = set()
    x = p - 1
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.add(d)
            x //= d
        d += 1
    if x > 1:
        fac.add(x)
    g = 2
    while not all(pow(g, (p - 1) // q, p) != 1 for q in fac):
        g += 1
    return g


def subgroup(p, n):
    g = gen(p)
    h = pow(g, (p - 1) // n, p)
    s = set()
    v = 1
    for _ in range(n):
        s.add(v)
        v = v * h % p
    return sorted(s)


def eta_real(p, mu, b):
    z = 2j * np.pi / p
    val = sum(np.exp(z * (b * x % p)) for x in mu)
    return val.real, abs(val.imag)


def legendre(b, p):
    r = pow(b, (p - 1) // 2, p)
    return 1 if r == 1 else (-1 if r == p - 1 else 0)


def find_prime(n, beta):
    target = int(n ** beta)
    p = target - (target % n) + 1
    for _ in range(400000):
        if p > n and sympy.isprime(p) and (p - 1) % n == 0:
            return p
        p += n
    return None


def sgn(re):
    return 1 if re > 1e-9 else (-1 if re < -1e-9 else 0)


print("n  | p        | beta | maxImEta | H1coset | H2legendre% | H3char-fails | H4 zeta-relsign const?")
for a in range(2, 7):
    n = 2 ** a
    for beta in (3.2, 4.0):
        p = find_prime(n, beta)
        if not p:
            continue
        g = gen(p)
        mu = subgroup(p, n)
        muset = set(mu)
        seen = set()
        reps = []
        for b in range(1, p):
            cb = frozenset((b * x) % p for x in mu)
            if cb not in seen:
                seen.add(cb)
                reps.append(b)
            if len(reps) >= 60:
                break
        signs = {}
        maxim = 0.0
        for b in reps:
            re, im = eta_real(p, mu, b)
            maxim = max(maxim, im)
            signs[b] = sgn(re)
        # H1: coset-constancy. recompute s at b*x for x in mu, compare.
        h1ok = True
        x0 = next(iter(muset))
        for b in reps[:8]:
            re2, _ = eta_real(p, mu, (b * x0) % p)
            if sgn(re2) != signs[b]:
                h1ok = False
        # H2
        m = tot = 0
        for b in reps:
            if signs[b] != 0:
                tot += 1
                if signs[b] == legendre(b, p):
                    m += 1
        h2pct = 100 * m / tot if tot else 0
        # H3 multiplicative
        h3fail = h3n = 0
        for i in range(min(15, len(reps))):
            for j in range(i, min(15, len(reps))):
                b1, b2 = reps[i], reps[j]
                bp = (b1 * b2) % p
                if bp == 0:
                    continue
                re, _ = eta_real(p, mu, bp)
                sp = sgn(re)
                if signs[b1] and signs[b2] and sp:
                    h3n += 1
                    if sp != signs[b1] * signs[b2]:
                        h3fail += 1
        # H4 zeta order 2n relative sign
        z2 = pow(g, (p - 1) // (2 * n), p) if (p - 1) % (2 * n) == 0 else None
        h4 = set()
        if z2:
            for b in reps[:20]:
                re, _ = eta_real(p, mu, (z2 * b) % p)
                sz = sgn(re)
                if signs[b] and sz:
                    h4.add(sz * signs[b])
        print(f"{n:3d}| {p:8d} | {beta} | {maxim:.1e} | {h1ok}    | {h2pct:5.1f}      | {h3fail}/{h3n}      | {sorted(h4)} const={len(h4) <= 1}")

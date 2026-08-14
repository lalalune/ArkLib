#!/usr/bin/env python3
"""
PROBE C14: Kloosterman-Sheaf Purity claim for the dyadic Gauss period (issue #444).

C14 claims: the Mann antipodal cosine sum eta_b = 2*sum cos(2 pi b x / p) over mu_n is the
Frobenius trace of a hyper-Kloosterman sheaf Kl_{n/2} with Sp/SL monodromy, so Deligne purity
gives |eta_b| <= 2*sqrt(n-1), pinning delta* past Johnson.

Tested against the HONESTY CONTRACT: proper subgroup mu_n (n=2^mu, n | p-1), p PRIME, p >> n^3,
NEVER n=p-1 (m=(p-1)/n strictly > 1, here m large). We measure M(n)=max_{b!=0}|eta_b| and compare:
  (i)   C14 claim         2*sqrt(n-1)
  (ii)  Johnson proxy     sqrt(n)
  (iii) BGK/prize target  sqrt(n log(p/n))
A SINGLE b with |eta_b| > 2 sqrt(n-1) REFUTES C14.

Also: for reference, the classical hyper-Kloosterman sum Kl_m(a;p) genuinely DOES satisfy
|Kl_m| <= m * p^{(m-1)/2} (Deligne) -- a p-DEPENDENT bound, NOT 2 sqrt(n-1). The point is that
eta_b is NOT a hyper-Kloosterman sum: it is a CYCLOTOMIC GAUSS PERIOD, a different object.
"""
import cmath, math
from sympy import isprime, primitive_root

def find_prime(n, beta):
    """p prime, n | p-1, p ~ n^beta (so p >> n^3 for beta>=4), m=(p-1)/n strictly > 1."""
    target = int(n**beta)
    cand = target - (target % n) + 1
    if cand <= target: cand += n
    while True:
        if isprime(cand) and (cand-1) % n == 0 and (cand-1)//n > 1:
            return cand
        cand += n

def mu_n(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    sub, x = [], 1
    for _ in range(n):
        sub.append(x); x = (x*h) % p
    assert len(set(sub)) == n
    return sub

def eta(b, sub, p):
    return sum(cmath.exp(2j*math.pi*((b*y) % p)/p) for y in sub)

def worstcase_eta(sub, p):
    # mu_n acts on frequencies: |eta_b| depends only on the coset b*mu_n, so sweep one rep
    # per coset of mu_n in F_p^* -> still need a representative set. Sweep all b for safety
    # but exploit |eta_{cb}|=|eta_b| for c in mu_n to cut work by factor n.
    seen = set()
    M, argmax = 0.0, None
    for b in range(1, p):
        if b in seen:
            continue
        for c in sub:
            seen.add((b*c) % p)
        v = abs(eta(b, sub, p))
        if v > M:
            M, argmax = v, b
    return M, argmax

print(f"{'mu':>3} {'n':>5} {'p':>10} {'p/n^3':>8} {'m':>8} {'M=max|eta|':>11} "
      f"{'2sqrt(n-1)':>11} {'C14?':>10} {'M/sqrt(n)':>10} {'sqrt(nlog)':>11}")
for mu in [3,4,5,6,7]:
    n = 2**mu
    beta = 4 if mu <= 6 else 3.4   # keep p tractable for the largest n while staying >> n^3
    p = find_prime(n, beta)
    sub = mu_n(n, p)
    m = (p-1)//n
    M, b = worstcase_eta(sub, p)
    c14 = 2*math.sqrt(n-1)
    verdict = "HOLDS" if M <= c14 + 1e-9 else "VIOLATED"
    print(f"{mu:>3} {n:>5} {p:>10} {p/n**3:>8.1f} {m:>8} {M:>11.3f} "
          f"{c14:>11.3f} {verdict:>10} {M/math.sqrt(n):>10.3f} "
          f"{math.sqrt(n*math.log(p/n)):>11.3f}")

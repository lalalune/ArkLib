#!/usr/bin/env python3
"""
C07 semiprimitive embedding (analyst: refuted-false).
Claim: the dyadic Gauss period over the prize prime is governed by the
SEMIPRIMITIVE Gauss-sum evaluation (Baumert-McEliece-..., -1 in <p> mod n),
which has an EXACT closed value eta = +-sqrt(q) up to sign -- a Johnson-or-better
explicit pin.  TRANSFER REQUIRES: the prize prime p is semiprimitive mod n,
i.e. there exists t with p^t == -1 (mod n).  We TEST that condition over proper
mu_n (p prime, p >> n^3, n | p-1, never n=p-1), n = 2^mu (the dyadic prize case).

If p is semiprimitive mod n, |eta_b| would all equal sqrt(n) exactly (the
semiprimitive degenerate-period fact).  We check BOTH:
  (a) does p^t == -1 mod n have a solution? (the semiprimitive condition)
  (b) is the actual sup |eta_b| equal to the semiprimitive value sqrt(n)?
A flip-to-survives would require (a) to hold AND (b) sqrt(n)-flat for the prize
prime -- which would be a closed Johnson-scale pin (=Johnson, not past it; but
crucially it would have to even HOLD).
"""
import sympy
from math import gcd, sqrt, cos, sin, pi

def find_p_and_subgroup(n, mult=100):
    target = n**4
    m = target // n
    while True:
        p = m * n + 1
        if sympy.isprime(p) and p > mult * n**3 and (p-1) != n:
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            mu = [pow(z, j, p) for j in range(n)]
            if len(set(mu)) == n:
                return p, z, mu
        m += 1

def semiprimitive_mod_n(p, n):
    """Does some power of p equal -1 mod n? i.e. is -1 in <p> mod (Z/n)^*?"""
    if gcd(p, n) != 1: return False, None
    neg1 = (-1) % n
    cur = 1 % n
    for t in range(1, 2*n+2):
        cur = (cur * p) % n
        if cur == neg1:
            return True, t
        if cur == 1 % n:  # cycled back without hitting -1
            break
    return False, None

def sup_period(p, z, n):
    """max_{b != 0} |sum_{y in mu_n} e_p(b*y)|.  Exact via cos/sin in float."""
    mu = [pow(z, j, p) for j in range(n)]
    best = 0.0
    best_b = None
    for b in range(1, p):  # too big in general; sample b over a coset rep set
        pass
    return None  # replaced below

def sup_period_sampled(p, z, n, nb=4000):
    mu = [pow(z, j, p) for j in range(n)]
    import random
    random.seed(1)
    bs = list(range(1, min(p, nb)))
    best = 0.0; best_b=None
    two_pi_over_p = 2*pi/p
    for b in bs:
        re=0.0; im=0.0
        for y in mu:
            ang = two_pi_over_p * ((b*y) % p)
            re += cos(ang); im += sin(ang)
        mag = sqrt(re*re+im*im)
        if mag > best:
            best = mag; best_b = b
    return best, best_b

print(f"{'n':>5} {'p':>12} {'p/n^3':>8} {'semiprim?':>10} {'t':>4} {'sup|eta|':>10} {'sqrt(n)':>9} {'ratio':>7}")
for mu in [3,4,5]:   # n = 8,16,32
    n = 2**mu
    p, z, _ = find_p_and_subgroup(n)
    sp, t = semiprimitive_mod_n(p, n)
    sup, bb = sup_period_sampled(p, z, n)
    rn = sqrt(n)
    print(f"{n:>5} {p:>12} {p/n**3:>8.2f} {str(sp):>10} {str(t):>4} {sup:>10.4f} {rn:>9.4f} {sup/rn:>7.3f}")

# Also: how often is a RANDOM dyadic prize prime semiprimitive? (measure-zero claim)
print("\n=== density: fraction of prize primes (n|p-1, p>>n^3) that are semiprimitive mod n ===")
for mu in [3,4,5,6]:
    n=2**mu
    cnt=0; tot=0
    target=n**4; m=target//n
    while tot<200:
        p=m*n+1; m+=1
        if sympy.isprime(p) and p>100*n**3 and (p-1)!=n:
            tot+=1
            sp,_=semiprimitive_mod_n(p,n)
            if sp: cnt+=1
    print(f"  n={n}: semiprimitive {cnt}/{tot} = {cnt/tot:.3f}")

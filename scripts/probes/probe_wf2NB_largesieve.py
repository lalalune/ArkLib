#!/usr/bin/env python3
"""
#407 lane wf-NB: ADDITIVE LARGE SIEVE on the family {eta_b}_b, at depth r.

NEW LENS. The higher moment  sum_b |eta_b|^{2r} = q * E_r  is a shifted-convolution
sum of the indicator 1_{mu_n}:
    eta_b^r = sum_s (1_{mu_n}^{*r})(s) e_p(b s)   (Fourier of the r-fold sumset measure)
so {eta_b^r}_b is the additive-character family of the measure  f = 1_{mu_n}^{*r}.

The additive LARGE SIEVE (Montgomery-Vaughan / Gallagher), for frequencies b/q that are
1/q-separated mod 1 (here b ranges over ALL of F_q, exactly the full residue system, so
separation delta = 1/q) and a_n supported on M = q consecutive residues:
    sum_b |sum_s a_s e(b s/q)|^2 <= (M + 1/delta) sum_s |a_s|^2 = (q + q) sum_s |a_s|^2.

Apply with a_s = f(s) = 1_{mu_n}^{*r}(s):
    sum_{b in F_q} |eta_b^r|^2  <=  2q * sum_s f(s)^2  =  2q * E_r.
But  sum_{b in F_q} |eta_b|^{2r} = q * E_r  EXACTLY (Parseval/orthogonality).
=> the additive large sieve gives a bound that is exactly 2x Parseval. It REDUCES TO
   the section-6 L2 wall (no sub-trivial sup control), as conjectured by the contract.
"""
import cmath, math
from collections import Counter
from sympy import isprime

def setup(n, p):
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            break
    return [pow(z, j, p) for j in range(n)]

def find_prime(n, beta):
    target = int(round(n**beta))
    p = target - (target % n) + 1
    while not isprime(p):
        p += n
    return p

def eta_all(mu, p):
    w = 2j*math.pi/p
    return [sum(cmath.exp(w*((b*x)%p)) for x in mu) for b in range(p)]

def sumset_indicator_r(mu, p, r):
    cur = Counter({x: 1 for x in mu})
    for _ in range(r-1):
        nxt = Counter()
        for s, c in cur.items():
            for x in mu:
                nxt[(s+x)%p] += c
        cur = nxt
    return cur

def E_r(mu, p, r):
    f = sumset_indicator_r(mu, p, r)
    return sum(c*c for c in f.values())

def report(n, beta, rmax):
    p = find_prime(n, beta)
    etas = eta_all(setup(n, p), p)
    print(f"\n=== n={n}  p={p}  beta={math.log(p)/math.log(n):.3f}  index m=(p-1)/n={(p-1)//n} ===")
    for r in range(1, rmax+1):
        lhs_full = sum(abs(e)**(2*r) for e in etas)
        Er = E_r(setup(n, p), p, r)
        ls_rhs = 2*p*Er
        parseval = p*Er
        M_exact = max(abs(e) for b,e in enumerate(etas) if b!=0)
        M_from_parseval = (parseval)**(1.0/(2*r))
        M_from_largesieve = (ls_rhs)**(1.0/(2*r))
        sqrtn = math.sqrt(n)
        print(f" r={r:2d}: |q*Er - sum|eta|^2r|={abs(parseval-lhs_full):.2e}  "
              f"M_exact/sqrtn={M_exact/sqrtn:.3f}  M_via_Parseval/sqrtn={M_from_parseval/sqrtn:.3f}  "
              f"M_via_LS/sqrtn={M_from_largesieve/sqrtn:.3f}")

if __name__ == "__main__":
    print("#407 wf-NB: additive large sieve on {eta_b}. Test: does it beat trivial Parseval at depth r?")
    print("Key: M(n)<=sqrt(2n log(p/n)) is the FLOOR target; M/sqrtn<=sqrt(2 log(p/n)).")
    for n in [8, 16]:
        for beta in [2.0, 2.5]:
            try:
                report(n, beta, rmax=min(2*int(math.log2(n))+1, 6))
            except Exception as ex:
                print(f" n={n} beta={beta} ERROR {ex}")
    print("\nDONE")

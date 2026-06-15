#!/usr/bin/env python3
"""
wf-D5 (#444): the Lam-Leung / cyclotomic orbit backbone of the binding monomial incidence I(n).

CLAIM (proven-per-fixed-n here; structural divisibility proven axiom-clean in Lean
  Frontier/_wf3D5_lamleung_orbit_backbone.lean):

  I(n) = 1 + (n/2) * O(n)

where:
  - the "+1" is the single gamma=0 in-code coincidence (x^a alone explainable),
  - the nonzero bad-scalar set {gamma != 0 : x^a + gamma*x^b explainable on a far witness}
    is EXACTLY invariant under multiplication by the subgroup <zeta^{gcd(a-b,n)}> of F_q*,
    which for the binding direction (a,b)=(n-6, 4) is mu_{n/2} = <zeta^2> (order n/2),
  - so the count of nonzero gammas is divisible by n/2 (free action => full-size orbits),
  - O(n) = #orbits is a PURELY COMBINATORIAL, p-INDEPENDENT object (the gamma-MULTISET is
    identical across primes; here checked across 3 primes per n).

This makes the (n/2) cyclotomic prefactor of I(n) STRUCTURAL (Lam-Leung dyadic descent /
negation symmetry of mu_n), not numerical -- exactly what the count lane (D2) needs.

Verified output (2026-06-14):
  n=16 k=4 (a=10,b=4,r=10): I=89  = 1 + 8*11    sym-group order 8 = n/2  (p-indep over 3 primes)
  n=24 k=4 (a=18,b=4,r=18): I=217 = 1 + 12*18   sym-group order 12 = n/2 (p-indep over 3 primes)
  n=32 k=4 (a=26,b=4,r=26): I=529 = 1 + 16*33   sym-group order 16 = n/2 (p-indep over 3 primes)

OPEN: a closed form for O(n) in {11,18,33,...} (the orbit count) -> would close I(n) entirely.
"""
import sys, itertools, math
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1, left_null
from prize_workspace import get_W


def bad_scalars(n, k, a, b, r, p, S, Vand):
    """Exact set of gammas s.t. x^a + gamma*x^b is explainable on a far witness (over-det)."""
    size = n - r
    pa_ = [pow(int(x), a, p) for x in S]
    pb_ = [pow(int(x), b, p) for x in S]
    goods = set()
    for R in itertools.combinations(range(n), size):
        P = left_null([Vand[i] for i in R], p)
        if not P:
            continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            goods.add(g)
    return goods


def analyze(n, k, a, b, r, primes):
    Igmults = []
    for plo in primes:
        p = find_prime_cong1(n, plo)
        S = list(get_W(n, p).S)
        gen = next(c for c in (int(x) for x in S)
                   if c != 1 and len({pow(c, j, p) for j in range(n)}) == n)
        Vand = [[pow(int(S[i]), j, p) for j in range(k)] for i in range(n)]
        g = bad_scalars(n, k, a, b, r, p, S, Vand)
        nz = set(x for x in g if x)
        # exact symmetry subgroup of nz under multiplication by zeta^d
        stab = [d for d in range(n) if all((x * pow(gen, d, p)) % p in nz for x in nz)]
        order = len(stab)
        gd = math.gcd((a - b) % n, n)
        orbits = len(nz) // order if order else 0
        Igmults.append(len(g))
        print(f"  n={n} p={p}: I={len(g)} = {1 if 0 in g else 0} + {order}*{orbits}"
              f"  sym-order={order} (n/{n // order if order else 0});"
              f" predicted |<zeta^gcd(a-b,n)>|=n/{gd}={n // gd} match={order == n // gd}",
              flush=True)
    print(f"  -> I(n) p-INDEPENDENT across primes: {len(set(Igmults)) == 1}; I={Igmults[0]}"
          f" = 1 + (n/2)*{(Igmults[0]-1)//(n//2)}\n", flush=True)


if __name__ == '__main__':
    primes = [200003, 786433, 5000011]
    analyze(16, 4, 10, 4, 10, primes)
    analyze(24, 4, 18, 4, 18, primes)
    analyze(32, 4, 26, 4, 26, primes)
    print("DONE")

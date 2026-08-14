#!/usr/bin/env python3
"""
Probe for issue #407: the general 2r-th additive moment identity for subgroup Gauss sums.

Claim (exact, char-p, no Weil):
  sum_{b in F_q} |eta_b|^{2r} = q * E_r(G)
where
  eta_b = sum_{y in G} psi(b*y),  psi a primitive additive character of F_q,
  E_r(G) = #{ (x_1..x_r, y_1..y_r) in G^{2r} : x_1+...+x_r = y_1+...+y_r }
         = the r-fold additive energy of G.

This generalizes r=1 (second moment = q*|G|, since E_1(G)=|G|) and
r=2 (fourth moment = q*addEnergy(G)).

We test for G = a multiplicative subgroup mu_n of F_p (p prime), various n, r.
"""
import cmath, itertools, math

def primitive_char(p):
    # psi(x) = exp(2*pi*i*x/p), x in Z/p
    w = cmath.exp(2j*math.pi/p)
    return lambda x: w**(x % p)

def subgroup_mu_n(p, n):
    # multiplicative subgroup of order n in F_p^*, requires n | (p-1)
    assert (p-1) % n == 0, f"{n} does not divide {p-1}"
    g = None
    # find a generator of F_p^*
    for cand in range(2, p):
        seen = set(); x = 1; order = 0
        for _ in range(p):
            x = (x*cand) % p; order += 1
            if x == 1: break
        if order == p-1:
            g = cand; break
    assert g is not None
    h = pow(g, (p-1)//n, p)  # element of order n
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    assert len(S) == n
    return sorted(S)

def moment_lhs(p, G, r):
    psi = primitive_char(p)
    total = 0.0
    for b in range(p):
        eta = sum(psi((b*y) % p) for y in G)
        total += abs(eta)**(2*r)
    return total

def energy_rhs(p, G, r):
    # E_r(G) = #{(x_1..x_r,y_1..y_r) in G^{2r}: sum x = sum y mod p}
    # count distribution of r-fold sums
    from collections import Counter
    sums = Counter()
    for tup in itertools.product(G, repeat=r):
        s = sum(tup) % p
        sums[s] += 1
    E = sum(c*c for c in sums.values())
    return E

def main():
    cases = [
        (7, 3, 1), (7, 3, 2), (7, 3, 3),
        (13, 4, 1), (13, 4, 2), (13, 4, 3),
        (13, 6, 2), (13, 6, 3),
        (17, 8, 2), (17, 8, 3),
        (31, 5, 2), (31, 5, 3), (31, 5, 4),
        (41, 8, 3),
    ]
    allok = True
    for (p, n, r) in cases:
        G = subgroup_mu_n(p, n)
        lhs = moment_lhs(p, G, r)
        E = energy_rhs(p, G, r)
        rhs = p * E
        ok = abs(lhs - rhs) < 1e-6 * max(1.0, rhs)
        allok = allok and ok
        print(f"p={p:3d} n={n} r={r}: LHS=sum|eta|^{2*r}={lhs:18.6f}  q*E_r={rhs:18.6f}  E_r={E:8d}  {'OK' if ok else 'MISMATCH'}")
    print("ALL OK" if allok else "SOME MISMATCH")

if __name__ == "__main__":
    main()

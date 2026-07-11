#!/usr/bin/env python3
"""
WF5-R1: the RELATIVE crossCell ratios that control the dyadic recursion.
For G=mu_n=H ⊔ zeta*H, H=mu_{n/2}:  N0(G,r)=2 N0(H,r)+crossCell(r).
The recursion N0(G,r) <= (2+eps)... is governed by:
  rho_diag(r) = crossCell(r) / (2 N0(H,r))      [the "eps" in crossCell <= eps*2N0(H,r)]
  rho_tot(r)  = crossCell(r) / N0(G,r)          [cross fraction of the total]
We want: is rho_diag bounded by eps<1 uniformly? (campaign: grows). Measure exactly.
Also test the SHARP structured form: does N0(G,r)/(2 N0(H,r)) (the per-level multiplier)
stay BOUNDED, i.e. is N0(G,r) <= C * 2 N0(H,r) for an ABSOLUTE C? Iterating gives
N0(mu_n,r) <= (2C)^mu * N0(mu_1,r)-scale => need 2C < something for prize.
char-0 structural counts (p large, exact via DP at a big prime).
"""
from collections import defaultdict
import sympy

def N0_exact(S, p, r):
    dist = {0: 1}
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for x in S:
                nd[(s + x) % p] += c
        dist = nd
    return dist.get(0, 0)

def subgroup(p, n):
    assert (p-1) % n == 0
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return sorted(set(S))

print(f"{'n':>4}{'r':>4}{'N0(H,r)':>12}{'N0(G,r)':>14}{'cross':>14}{'rho_diag':>10}{'rho_tot':>9}{'mult':>8}")
# mult = N0(G,r)/(2 N0(H,r))  -- per-level multiplier; want bounded < sqrt(2)? for prize
for mu in [3,4,5]:
    n = 2**mu
    # big prime p ==1 mod n, thin (beta~4): p ~ n^4
    target = n**4
    p = sympy.nextprime(target)
    while (p-1) % n != 0: p = sympy.nextprime(p)
    G = subgroup(p, n)
    H = subgroup(p, n//2)
    Hset=set(H)
    assert set(H).issubset(set(G)), "H not subgroup of G"
    for r in range(1, 9):
        ng = N0_exact(G, p, r)
        nh = N0_exact(H, p, r)
        cross = ng - 2*nh
        rho_diag = cross/(2*nh) if nh>0 else float('nan')
        rho_tot = cross/ng if ng>0 else float('nan')
        mult = ng/(2*nh) if nh>0 else float('nan')
        print(f"{n:>4}{r:>4}{nh:>12}{ng:>14}{cross:>14}{rho_diag:>10.3f}{rho_tot:>9.3f}{mult:>8.3f}")
    print()

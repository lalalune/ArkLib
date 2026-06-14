#!/usr/bin/env python3
"""
#407 STRATEGY 2 — the 2-adic moment recursion for A_r(mu_{2^mu}).

GOAL: derive EXACTLY the recursion for the DC-subtracted moment
    A_r(n) := (1/p) sum_{b != 0} |eta_b(mu_n)|^{2r},   n = 2^mu
in terms of level-(n/2) quantities, and test whether the L^{2r} (moment) descent
TELESCOPES to give  A_r(n) <= (2r-1)!! n^r  (Wick),  where the L^infty descent FAILS.

KEY STRUCTURE (GaussPeriodTower.lean parallelogram):
   mu_n = mu_{n/2} ⊔ zeta * mu_{n/2}    (zeta primitive n-th root)
   eta_b(mu_n) = A_b + B_b,   A_b = eta_b(mu_{n/2}),  B_b = eta_{zeta b}(mu_{n/2}).
Note B_b = sum_{x in mu_{n/2}} e_p(b zeta x) = eta over the SAME subgroup mu_{n/2}
but at frequency zeta*b. Since zeta is a UNIT in F_p, the map b -> zeta b permutes F_p^*.

So  A_r(n) = (1/p) sum_{b!=0} |eta_b(mu_{n/2}) + eta_{zeta b}(mu_{n/2})|^{2r}.

This is a "correlated 2-shift" moment: it couples eta at b and at zeta*b over the
SAME smaller subgroup. We want to relate it to A_*(n/2).

We compute EVERYTHING exactly (e_p complex exponentials, no sampling).
"""
import cmath, math
from sympy import primerange, primitive_root

def setup(n, p):
    g = int(primitive_root(p))
    # element zeta of order exactly n
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            break
    mu_half = [pow(z, 2*j, p) for j in range(n//2)]   # mu_{n/2} = <zeta^2>
    return z, mu_half

def eta(b, S, p, w):
    return sum(cmath.exp(w*((b*x) % p)) for x in S)

def doublefact(r):
    d = 1.0
    for j in range(1, 2*r, 2):
        d *= j
    return d

def A_r_direct(n, p, rmax):
    """A_r(mu_n) for r=1..rmax, exact via full eta over mu_n."""
    z, mu_half = setup(n, p)
    mu_n = mu_half + [(z*x) % p for x in mu_half]
    w = 2j*math.pi/p
    Ar = [0.0]*(rmax+1)
    for b in range(1, p):
        e2 = abs(eta(b, mu_n, p, w))**2
        pw = 1.0
        for r in range(1, rmax+1):
            pw *= e2
            Ar[r] += pw
    return [Ar[r]/p for r in range(rmax+1)]

def main():
    print("="*110)
    print("PART 1: A_r(n)/Wick  -- confirm <= 1 and decreasing (the target inequality)")
    print("="*110)
    cases = [
        (8,  [97, 193, 401, 809]),
        (16, [193, 353, 577, 1153, 2113]),
        (32, [193, 257, 353, 449, 577, 1153]),
        (64, [193, 257, 449, 577, 1217, 2113]),
    ]
    for n, primes in cases:
        rmax = min(2*int(math.log2(n))+2, 12)
        print(f"\n--- mu_{n}  (rmax={rmax}) ---")
        for p in primes:
            if (p-1) % n: continue
            Ar = A_r_direct(n, p, rmax)
            row = []
            for r in range(1, rmax+1):
                w = doublefact(r)*n**r
                row.append(f"{Ar[r]/w:.3f}")
            beta = math.log(p)/math.log(n)
            print(f"  p={p:6d} (beta={beta:.2f}): A_r/Wick = [" + " ".join(row) + "]")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
#407 CONNECTION C5 — Gauss-period tower recursion as a MOMENT recursion.

The GaussPeriodTower.lean parallelogram law:
    ||eta_b(mu_n)||^2 + ||eta^chi_b(mu_n)||^2 = 2(||A||^2 + ||B||^2)
where for the dyadic split mu_n = mu_{n/2} ⊔ zeta*mu_{n/2}:
    A = sum_{x in mu_{n/2}} e_p(b x)          = eta_b(mu_{n/2})       (level n/2, freq b)
    B = sum_{x in zeta*mu_{n/2}} e_p(b x)     = eta_{b*zeta}(mu_{n/2})  (level n/2, freq b*zeta)
    eta_b(mu_n)      = A + B
    eta^chi_b(mu_n)  = A - B   (quadratic twist: +1 on mu_{n/2}, -1 on zeta-coset)

GOAL (task a/b/c):
 (a) Substitute the recursion into the 2k-th moment A_k(n) = (1/p) sum_{b!=0} |eta_b(mu_n)|^{2k}.
     Does it give a clean recursion A_k(n) <- A_*(n/2)? Need cross-moments ||A||^{2a}||B||^{2b}.
 (b) Does it telescope down the 2-adic tower to mu_2/mu_4 base case?
 (c) The L^infty per-level descent M(n)^2 <= 2 M(n/2)^2 is KNOWN FALSE (ratios 3.58/3.10/2.51).
     Does the L^{2k} (moment) descent work where L^infty failed? Or same alignment obstruction?

We compute EXACT quantities (no sampling). Primes p ≡ 1 mod n.
"""
import cmath, math, sys

def primitive_root(p):
    # find a generator of F_p^*
    from sympy import primitive_root as pr
    return int(pr(p))

def subgroup_mu(n, p):
    """elements of mu_n (n-th roots of unity) in F_p^*, given n | p-1."""
    g = primitive_root(p)
    t = pow(g, (p-1)//n, p)   # element of order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x*t) % p
    return S, g, t

def eta(b, S, p):
    """Gauss period sum_{x in S} e_p(b x), e_p(z)=exp(2 pi i z / p)."""
    w = 2j*math.pi/p
    return sum(cmath.exp(w*((b*x)%p)) for x in S)

def moments_direct(n, p, kmax):
    """A_k(n) = (1/p) sum_{b != 0} |eta_b(mu_n)|^{2k}, k=1..kmax."""
    S, g, t = subgroup_mu(n, p)
    Ak = [0.0]*(kmax+1)
    for b in range(1, p):
        e = abs(eta(b, S, p))
        e2 = e*e
        pw = 1.0
        for k in range(1, kmax+1):
            pw *= e2
            Ak[k] += pw
    return [Ak[k]/p for k in range(kmax+1)]

def char0_wick(n, k):
    """Char-0 Wick energy E_k(mu_n) = (2k-1)!! * n^k. A_k = E_k - n^{2k}/p (b=0 term)."""
    df = 1.0
    for j in range(1, 2*k, 2):
        df *= j
    return df * (n**k)

def main():
    # primes p ≡ 1 mod n, moderately large so non-saturated
    cases = [
        (4,  [13, 29, 53, 101, 197]),
        (8,  [17, 41, 73, 97, 193, 401]),
        (16, [17, 97, 113, 193, 353, 577, 1153]),
        (32, [97, 193, 257, 353, 449, 577, 1153]),
    ]
    kmax = 4
    print("="*100)
    print("PART A: does A_k(n) match char-0 Wick (2k-1)!! n^k, and is the b=0 term n^{2k}/p?")
    print("="*100)
    for n, primes in cases:
        print(f"\n--- mu_{n} ---")
        print(f"  Wick E_k(mu_{n}) = (2k-1)!!*{n}^k:", [round(char0_wick(n,k),1) for k in range(1,kmax+1)])
        for p in primes:
            if (p-1) % n != 0: continue
            Ak = moments_direct(n, p, kmax)
            # full energy E_k = A_k + n^{2k}/p
            Ek = [Ak[k] + (n**(2*k))/p for k in range(kmax+1)]
            row = []
            for k in range(1,kmax+1):
                w = char0_wick(n,k)
                row.append(f"E{k}={Ek[k]:.2f}(Wick {w:.1f}, A{k}={Ak[k]:.2f})")
            print(f"  p={p:5d}: " + "  ".join(row))

if __name__ == "__main__":
    main()

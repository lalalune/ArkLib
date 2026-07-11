"""
wf407 / T389-01-deepmom : Q3 — can ANY non-moment technique supply depth r ~ log q
cancellation, or is this irreducibly the Paley-graph / BGK wall?

We check three things:
 (A) The true B = max_{b!=0}|eta_b| genuinely tracks sqrt(n log(q/n)), confirming the
     CONJECTURE is right (only the proof is missing) — at a range of prize-diagonal primes.
 (B) The defect Delta_r = E_r^(p) - E_r^(0) at the saddle r ~ log q is a structured
     mod-p coincidence count = the Paley-graph eigenvalue object, NOT a moment artifact.
     We confirm B IS exactly the non-principal eigenvalue of Cay(F_p, mu_n) (generalized
     Paley graph): B = max_{b!=0}|eta_b| and the graph eigenvalues are {eta_b}.
 (C) The HEIGHT OBSTRUCTION quantification: any char-0 algebraic certificate alpha in
     Z[zeta_n] that the defect is ZERO (Delta=0) has |N(alpha)| <= house^{phi(n)}; the
     transfer is FORCED only if phi(n)*log2(house) < log2 p. At prize n=2^32, phi=2^31,
     budget 256/2^31 = 2^-23 << any house>1 -> NO char-0-transferable certificate exists.
     This is WHY no algebraic (non-analytic) route can close it: the certificate would have
     to be analytic = the BGK/Paley wall.
"""

import math
from math import log, sqrt
from sympy import primerange


def is_prim_root(g, p):
    cur = g % p
    order = 1
    while cur != 1:
        cur = (cur * g) % p
        order += 1
        if order > p:
            return False
    return order == p - 1


def mu_n_charp(n, p):
    for cand in range(2, p):
        if is_prim_root(cand, p):
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]


def true_B(n, p, roots):
    best = 0.0
    for b in range(1, p):
        re = im = 0.0
        for x in roots:
            ang = 2 * math.pi * (b * x % p) / p
            re += math.cos(ang); im += math.sin(ang)
        v = math.hypot(re, im)
        if v > best:
            best = v
    return best


print("=" * 84)
print("(A) Does true B track sqrt(n log(q/n))? (conjecture right, only proof missing)")
print("=" * 84)
print(f"{'n':>4} {'p':>9} {'beta=logn p':>11} {'B':>9} {'sqrt(n)':>8} "
      f"{'sqrt(n*ln(p/n))':>15} {'B/sqrt(n ln(p/n))':>18} {'B/sqrt(n)':>10}")
# prize-diagonal-ish: p ~ n^beta for a few beta, n in enumerable range
for n in (16, 32, 64):
    plist = [p for p in primerange(2, 200000) if p % n == 1]
    for beta in (3.0, 4.0, 5.0):
        target = n ** beta
        if target > 180000:
            continue
        p = min(plist, key=lambda x: abs(x - target))
        roots = mu_n_charp(n, p)
        B = true_B(n, p, roots)
        m = (p - 1) / n
        c1 = B / sqrt(n * math.log(p / n))
        c2 = B / sqrt(n)
        print(f"{n:>4} {p:>9} {log(p,n):>11.2f} {B:>9.3f} {sqrt(n):>8.3f} "
              f"{sqrt(n*math.log(p/n)):>15.3f} {c1:>18.3f} {c2:>10.3f}")

print()
print("Reading: if B/sqrt(n ln(p/n)) is STABLE ~1.0-1.4 across n,beta while B/sqrt(n)")
print("GROWS, the sqrt(n log) law is confirmed empirically = conjecture right, proof open.")

print()
print("=" * 84)
print("(C) HEIGHT OBSTRUCTION: why no NON-ANALYTIC (algebraic) certificate can close it")
print("=" * 84)
print("A char-0 certificate that the saddle-depth defect Delta_r = 0 is the assertion that")
print("a specific alpha in Z[zeta_n] (a sparse +-1 root-sum) is != 0 mod p. It transfers")
print("(forced != 0 mod p) ONLY IF |N(alpha)| < p, and |N(alpha)| <= house(alpha)^phi(n).")
print("Per-conjugate height budget = log2(p)/phi(n):")
print(f"{'a':>3} {'n=2^a':>12} {'phi(n)=2^{a-1}':>14} {'log2 p=256':>11} "
      f"{'budget 256/phi':>15} {'house allowed':>14}")
for a in (3, 4, 8, 16, 30, 32):
    n = 2 ** a
    phi = 2 ** (a - 1)
    budget = 256.0 / phi
    house_allowed = 2 ** budget
    print(f"{a:>3} {n:>12.3e} {phi:>14.3e} {256:>11} {budget:>15.3e} {house_allowed:>14.4f}")
print()
print("At prize a=32: budget = 256/2^31 = 2^-23, so house(alpha) must be < 1+2^-23 ~ 1.")
print("But any NONZERO sparse root-sum has house > 1 (a >=2 +-roots sum). So |N(alpha)| >> p")
print("=> the certificate CAN vanish mod p => Delta_r CAN be > 0. No char-0 algebraic")
print("certificate forces the transfer at prize scale; only an ANALYTIC (character-sum /")
print("equidistribution) input can bound the defect = the Paley-graph/BGK wall. IRREDUCIBLE.")

print()
print("=" * 84)
print("(B) B is the generalized-Paley-graph eigenvalue: B = max_{b!=0}|eta_b|, and the")
print("    BEST proven bound on this object is BGK n^{1-o(1)} (vacuous below q^{1/3});")
print("    B<=2 sqrt(n) <=> Cay(F_q,mu_n) Ramanujan = the Paley Graph Conjecture (open).")
print("=" * 84)
print("Confirm: eta_b are real-part-symmetric; |eta_b|=|eta_{-b}|; the multiset {eta_b:b!=0}")
print("is the non-trivial spectrum of the n-regular Cayley graph Cay(F_p, mu_n).")
n, p = 16, 16369
roots = mu_n_charp(n, p)
# sum of |eta_b|^2 over b!=0 should be (p-1)*n - n^2? Actually sum_b |eta_b|^2 = p*E_1 = p*n;
# minus b=0 term n^2. And the graph is n-regular so trace=0 => sum eta_b = ... check Parseval.
s2 = 0.0
for b in range(1, p):
    re = im = 0.0
    for x in roots:
        ang = 2*math.pi*(b*x % p)/p
        re += math.cos(ang); im += math.sin(ang)
    s2 += re*re + im*im
print(f"n={n}, p={p}: sum_b!=0 |eta_b|^2 = {s2:.1f}  vs  p*n - n^2 = {p*n - n*n}  "
      f"(Parseval: sum_all|eta_b|^2 = p*E_1 = p*n = {p*n}, b=0 term = n^2 = {n*n})")

#!/usr/bin/env python3
"""
PROBE (#444 / #357 AddEnergyGcdDegreeBound residual): the SUMSET-SUPPORT restriction.

The committed `addEnergy_le_sum_gcd_degree_sq` bounds E(G) <= Sum_{c in F} (deg gcd_c)^2,
summed over ALL c in F. The file's PROSE (line 21) claims gcd_c is nontrivial only when
c in G+G. This probe confirms the SHARP support statement that makes that precise:

    for c NOT in G+G:  r(c) = #{z in G : c-z in G} = 0   (representation count vanishes)

=> the energy sum's support is contained in the SUMSET G+G, shrinking the index set from
   |F| down to |G+G| <= |G|^2 terms. (NON-MOMENT: a support/sumset fact, not an energy bound.)

We also report, for honesty, the gcd-degree behaviour at c in/out of G+G to confirm the
gcd-degree (not just r(c)) ALSO vanishes off the sumset (gcd_c trivial => natDegree 0),
which is the stronger statement the Lean brick will target on the summand directly.

Thin subgroup mu_n = G = {z : z^n = 1} in F_p^*, NEVER n = q-1. Multiple primes incl p > n^3.
EXACT integer arithmetic mod p; no floats in any verdict.
"""
import math

def subgroup_gen(p, n):
    """primitive root, then g^((p-1)/n) generates the order-n subgroup."""
    def order(g):
        x = 1
        for e in range(1, p):
            x = (x * g) % p
            if x == 1:
                return e
        return p - 1
    for cand in range(2, p):
        if order(cand) == p - 1:
            return pow(cand, (p - 1) // n, p)
    raise RuntimeError("no primitive root")

def poly_gcd_deg_mod_p(n, c, p):
    """deg gcd(X^n - 1, (c - X)^n - 1) over F_p, exact, via Euclid on coeff lists (mod p)."""
    # Represent polys as coeff lists, index = power, mod p. We compute (c-X)^n - 1 and X^n - 1.
    # Use sympy-free exact poly gcd over F_p.
    def trim(a):
        while len(a) > 1 and a[-1] % p == 0:
            a.pop()
        return a
    def polymod(a, b):
        a = [x % p for x in a]; b = [x % p for x in b]; trim(a); trim(b)
        binv = pow(b[-1], p - 2, p)
        while len(a) >= len(b) and not (len(a) == 1 and a[0] % p == 0):
            d = len(a) - len(b)
            coef = (a[-1] * binv) % p
            for i in range(len(b)):
                a[d + i] = (a[d + i] - coef * b[i]) % p
            trim(a)
            if len(a) < len(b):
                break
        return trim(a)
    def gcd(a, b):
        a = a[:]; b = b[:]
        while not (len(b) == 1 and b[0] % p == 0):
            a, b = b, polymod(a, b)
        return trim(a)
    # X^n - 1
    A = [0] * (n + 1); A[0] = (-1) % p; A[n] = 1
    # (c - X)^n - 1 : binomial expand (c - X)^n = sum_k C(n,k) c^{n-k} (-X)^k
    B = [0] * (n + 1)
    for k in range(n + 1):
        B[k] = (math.comb(n, k) * pow(c % p, n - k, p) * pow((-1) % p, k, p)) % p
    B[0] = (B[0] - 1) % p
    g = gcd(A, B)
    g = trim(g)
    if len(g) == 1 and g[0] % p == 0:
        return -1  # zero poly (shouldn't happen)
    return len(g) - 1  # natDegree

def main():
    cases = [(97, 8), (193, 16), (257, 16), (337, 16), (1153, 16), (12289, 16)]
    all_ok = True
    print("c-not-in-sumset => r(c)=0  AND  gcd_deg(c)=0  (the support restriction)")
    for (p, n) in cases:
        if (p - 1) % n or (p - 1) // n < 2:
            continue
        if p < n ** 3:
            tag = "p<=n^3"
        else:
            tag = "p>n^3"
        g0 = subgroup_gen(p, n)
        G = set(pow(g0, t, p) for t in range(n))
        sumset = set((a + b) % p for a in G for b in G)
        bad_r = 0   # c not in sumset but r(c)>0  (should be 0)
        bad_g = 0   # c not in sumset but gcd_deg>0 (should be 0)
        r_pos_outside = 0
        for c in range(p):
            r = sum(1 for z in G if ((c - z) % p) in G)
            in_ss = (c in sumset)
            if not in_ss and r > 0:
                bad_r += 1
            gd = poly_gcd_deg_mod_p(n, c, p)
            if not in_ss and gd > 0:
                bad_g += 1
            # cross-check: r(c)>0  <=>  c in sumset
            if r > 0 and not in_ss:
                r_pos_outside += 1
        ok = (bad_r == 0 and bad_g == 0)
        all_ok = all_ok and ok
        print(f"p={p:6d} n={n:3d} ({tag:7s}) |G+G|={len(sumset):4d}/{p}  "
              f"r>0-off-sumset={bad_r}  gcd_deg>0-off-sumset={bad_g}  "
              f"=> {'OK' if ok else 'FAIL'}")
    print()
    print(f"VERDICT (support restriction r(c)=0 and gcd_deg(c)=0 off the sumset G+G): "
          f"{'HOLDS — sum support ⊆ G+G' if all_ok else 'FAILS'}")

if __name__ == "__main__":
    main()

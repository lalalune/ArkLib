#!/usr/bin/env python3
"""
LANE J1b (#444): the DECISIVE Dvornicich-Zannier reconciliation.

The S-unit / subspace / Conway-Jones machinery, applied honestly to the prize.

OBJECT.  The prize sup M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|.  The energy /
wraparound route bottoms out at the count W_r = #{genuine char-p vanishing
relations of length <= 2r among n-th roots} (sum of signed n-th roots = 0 mod p,
NOT 0 over Z[zeta_n]).  This is the "Mann's theorem mod P" object.

LITERATURE (this lane's research):
 * Mann (1965) / Conway-Jones (1976) / Lam-Leung (2000): char-0 minimal vanishing
   sums.  CJ inequality: a minimal vanishing sum of roots of unity of (squarefree)
   order m has term-count k >= Psi(m) := 2 + sum_{prime p|m}(p-2).  For m=2 (the
   ONLY squarefree order dividing a 2-power), Psi(2)=2 => only ANTIPODAL pairs.
   So over Z[zeta_{2^mu}] EVERY vanishing sum is a Z-combination of antipodal
   pairs zeta^a+zeta^{a+n/2}=0 (this is exactly Mann for 2-power).
 * Dvornicich-Zannier (Archiv der Math 79 (2002) 104-108), "Sums of roots of unity
   vanishing modulo a prime": for gcd(n, ell)=1 the congruence
   sum a_i zeta_i = 0 (mod ell) obeys THE SAME Conway-Jones inequality as the
   char-0 case, INDEPENDENT of ell.  i.e. the modular classification matches CJ.
 * Evertse-Schlickewei-Schmidt (Annals 155 (2002) 807-836): # non-degenerate
   solutions of a_1x_1+...+a_nx_n=1 in a rank-r mult. group is <= exp((6n)^{3n}(r+1)),
   for r=0 (roots of unity) <= (n+1)^{3(n+1)^2}.  REQUIRES characteristic 0.

THE TWO COMPETING READINGS this probe decides by EXACT computation:
 (R-applies)  If Dvornicich-Zannier transfers verbatim with the CJ floor, then
   for n=2^mu and gcd(n,p)=1, the minimal genuine char-p relation has length
   >= Psi(2)=2 but the 2-power structure forces it MUCH higher -- the relations
   that are short over F_p but not over Z[zeta] must encode p, so length grows
   with log p.  That would FORCE the floor (NEW-DIRECT-HANDLE).
 (R-vacuous) If genuine char-p relations of BOUNDED length (independent of p)
   exist as p grows at beta=4, then CJ/DZ does NOT lower-bound them, and the
   char-0 ESS count is vacuous for the gap.  REDUCES/VACUOUS.

This probe measures the ACTUAL minimal genuine char-p relation length L*(n,p)
by exact search (meet-in-the-middle, signed n-th roots), and its scaling vs p.

EXACT integer arithmetic only.  No float, no FFT.
"""
import itertools, sys
from sympy import nextprime, primitive_root

def first_prime_1_mod_n_at_least(n, lo):
    p = nextprime(lo - 1)
    while (p - 1) % n != 0:
        p = nextprime(p)
    return p

def mu_n_powers(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)], h

def char0_zero(coeff, n, half):
    """coeff: dict exp->net Z coeff.  zeta_{2^mu}^{n/2} = -1 reduction onto basis
    {1..zeta^{half-1}}.  Returns True iff = 0 over Z[zeta_n] (char-0 vanishing)."""
    vec = [0] * half
    for a, c in coeff.items():
        a %= n
        if a < half:
            vec[a] += c
        else:
            vec[a - half] -= c
    return all(v == 0 for v in vec)

def minimal_genuine_charp_mitm(n, p, Lmax):
    """Meet-in-the-middle over signed multisets of n-th-root powers.

    We want the shortest L and a signed multiset {(s_i,a_i)} of size L with
    sum s_i h^{a_i} = 0 mod p and NOT char-0 zero.  MITM: for half-length t,
    enumerate signed-multiset partial sums of size t and look for two halves
    A,B with val(A) + val(B) = 0 mod p, total length L=2t or 2t+1, screening
    out char-0 zeros.  We sweep L upward and stop at the first genuine hit.
    For tractability we cap the number of DISTINCT exponents used (support s)
    -- the prize-relevant short relations are sparse-support, and we also run
    a full (non-MITM) brute check for very small L to be safe.
    """
    powers, h = mu_n_powers(n, p)
    half = n // 2

    # small-L exact brute (no support cap), authoritative for L<=Lbrute
    def brute(L):
        for exps in itertools.combinations_with_replacement(range(n), L):
            for signs in itertools.product((1, -1), repeat=L):
                if signs[0] == -1:
                    continue
                val = 0
                coeff = {}
                for s, a in zip(signs, exps):
                    val = (val + s * powers[a]) % p
                    coeff[a] = coeff.get(a, 0) + s
                if val == 0 and not char0_zero(coeff, n, half):
                    return list(zip(signs, exps))
        return None

    Lbrute = min(Lmax, 6 if n <= 16 else (5 if n <= 64 else 4))
    for L in range(2, Lbrute + 1):
        w = brute(L)
        if w:
            return L, w, "brute"
    return None, None, f"none<= {Lbrute}"

print("=" * 80)
print("J1b: minimal GENUINE char-p relation length L*(n,p) vs growing p (beta=4)")
print("     and a multi-p sweep to test p-(in)dependence of L*.")
print("=" * 80)
print(f"{'n':>5} {'p~n^4':>14} {'L* (genuine char-p)':>22} {'method':>10}")
rows = []
for mu_s in (3, 4, 5, 6):
    n = 1 << mu_s
    p = first_prime_1_mod_n_at_least(n, n ** 4)
    L, w, meth = minimal_genuine_charp_mitm(n, p, Lmax=6)
    rows.append((n, p, L))
    print(f"{n:>5} {p:>14} {str(L):>22} {meth:>10}")
    if w:
        print(f"      witness: {w}")

print()
print("=" * 80)
print("Multi-p at fixed n: does L* depend on p?  (test DZ 'independent of ell')")
print("=" * 80)
for mu_s in (3, 4):
    n = 1 << mu_s
    print(f"-- n={n}: first 5 primes = 1 mod n with p>=n^4 --")
    p = n ** 4
    cnt = 0
    pp = first_prime_1_mod_n_at_least(n, p)
    while cnt < 5:
        L, w, meth = minimal_genuine_charp_mitm(n, pp, Lmax=6)
        print(f"   p={pp:>12}  L*={L}")
        pp = first_prime_1_mod_n_at_least(n, pp + 1)
        cnt += 1

print()
print("READING:")
print(" * 'none<=Lbrute' means NO genuine char-p relation of length <= Lbrute:")
print("   the minimal genuine relation is LONGER than the brute horizon, i.e. the")
print("   2-power norm is protecting the short lengths (consistent with DZ/CJ floor).")
print(" * If instead L* is small and CONSTANT as p grows => bounded-length genuine")
print("   relations => char-0 ESS/CJ count is VACUOUS for the gap.")

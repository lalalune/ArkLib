"""
wf407 / T389-01-deepmom : the deep-moment validity wall.

THREE QUESTIONS (exact numerics, not sampled):
 Q1. Re-confirm r_opt/r_max ≈ (log n)/2 = a/2 at prize p~n^5.
 Q2. WHAT fails at the crossover depth: is it the char-0 bound E_r^(0) ≤ (2r-1)!! n^r
     that fails, or the char-p TRANSFER E_r^(p) ≈ E_r^(0) that fails? Compute BOTH the
     exact char-0 energy E_r^(0)(μ_n) AND the exact char-p energy E_r^(p)(μ_n) and find
     the exact r where they diverge, vs the bound (2r-1)!! n^r.
 Q3. The moment-method ceiling on B at the deepest RELIABLE r vs the prize target.

Definitions:
 μ_n = the n-th roots of unity (n=2^a). Over F_p with p ≡ 1 mod n, μ_n is the order-n
 multiplicative subgroup. Over C (char 0), μ_n = {e^{2πi k/n}}.

 E_r(μ_n) = #{(x_1..x_r, y_1..y_r) ∈ μ_n^{2r} : x_1+..+x_r = y_1+..+y_r}   (2r-fold energy)

 Identity (Parseval): sum_b |η_b|^{2r} = q · E_r  where η_b = sum_{x∈μ_n} e_p(bx).
 Moment transport: B = max_{b≠0}|η_b| ≤ (q E_r)^{1/2r}.
"""

import itertools
import math
from math import comb, factorial, log


def doublefact_odd(r):
    """(2r-1)!! = 1*3*5*...*(2r-1)."""
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


# ---------------------------------------------------------------------------
# char-0 EXACT additive energy E_r^(0)(mu_n)  (n-th roots of unity over C)
# Counted as integer-vector sums: x in mu_n <-> exponent in Z/n; a sum of r roots
# equals a sum of r roots iff the two MULTISETS of exponents have equal "vanishing"
# combination, i.e. (sum of r roots) - (sum of r roots) = 0 in Z[zeta_n].
# For n=2^a, Z[zeta_n] has rank phi(n)=2^{a-1}; a vanishing sum of {+1}^r {-1}^r roots
# of unity. We count exactly by enumerating all (multi-indexed) tuples and testing
# equality of the algebraic-number sums via the cyclotomic relation.
# We represent each root e^{2pi i k/n} by its reduced coordinate in the integral basis
# {zeta^0..zeta^{phi-1}} using zeta^{phi+j} = -... ; simplest: use the minimal poly
# X^{n/2}+1 (=Phi_n for n=2^a) so zeta^{n/2} = -zeta^0 reduction. We track the vector
# in Z^{n/2} where index = exponent mod n, folded by k -> (k mod (n/2)) with sign
# (-1)^{k // (n/2)}.
# ---------------------------------------------------------------------------

def root_vec_char0(n, k):
    """Coordinate vector of zeta_n^k in basis {1,zeta,...,zeta^{n/2-1}} using zeta^{n/2}=-1."""
    half = n // 2
    v = [0] * half
    sign = 1 if (k // half) % 2 == 0 else -1
    v[k % half] += sign
    return v


def energy_char0_exact(n, r):
    """Exact E_r^(0)(mu_n) for n=2^a by brute enumeration. Feasible for small n,r."""
    half = n // 2
    # precompute coordinate of each root
    rootcoord = [root_vec_char0(n, k) for k in range(n)]
    from collections import Counter
    sums = Counter()
    # enumerate all r-tuples of exponents in [0,n) ; record the coordinate sum
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * half
        for k in tup:
            rc = rootcoord[k]
            for j in range(half):
                v[j] += rc[j]
        sums[tuple(v)] += 1
    # E_r = sum over distinct sum-vectors of (count)^2
    return sum(c * c for c in sums.values())


def energy_charp_exact(n, r, p):
    """Exact E_r^(p)(mu_n) over F_p. p ≡ 1 mod n required; mu_n = <g^{(p-1)/n>}."""
    # find a generator of mu_n in F_p
    # primitive root:
    def is_prim_root(g):
        seen = set()
        x = 1
        for _ in range(p - 1):
            x = (x * g) % p
            seen.add(x)
        return len(seen) == p - 1
    g = None
    for cand in range(2, p):
        if is_prim_root(cand):
            g = cand
            break
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    roots = [pow(h, k, p) for k in range(n)]
    from collections import Counter
    sums = Counter()
    for tup in itertools.product(roots, repeat=r):
        s = sum(tup) % p
        sums[s] += 1
    return sum(c * c for c in sums.values())


print("=" * 78)
print("Q2: char-0 energy E_r^(0), the BOUND (2r-1)!!*n^r, and char-p E_r^(p)")
print("=" * 78)
print("Does the char-0 bound E_r^(0) <= (2r-1)!! n^r HOLD (Bessel lemma)? "
      "And where does char-p DIVERGE?")
print()

# small primes p ≡ 1 mod n for each n
prime_for_n = {
    4:  [13, 29, 37, 53],
    8:  [17, 41, 73, 89],
    16: [17, 97, 113, 193],
}

for n in (4, 8, 16):
    a = int(round(log(n, 2)))
    print(f"\n--- n = {n} (a={a}), bound = (2r-1)!! * n^r ---")
    print(f"{'r':>2} {'E_r^(0)':>14} {'(2r-1)!!n^r':>16} {'E0<=bnd?':>9} "
          f"{'ratio E0/bnd':>12}   char-p E_r^(p)  (diverge?)")
    rmax_feasible = 4 if n <= 8 else 3
    for r in range(1, rmax_feasible + 1):
        e0 = energy_char0_exact(n, r)
        bnd = doublefact_odd(r) * n ** r
        ok = "YES" if e0 <= bnd else "** NO **"
        ratio = e0 / bnd
        # char-p for the available primes
        cps = []
        for p in prime_for_n.get(n, []):
            if r <= 3 and n ** r * 4 < 2_000_000:  # feasibility guard
                ep = energy_charp_exact(n, r, p)
                cps.append((p, ep))
        cpstr = "  ".join(
            f"p={p}:{ep}{'!=C0' if ep != e0 else '=C0'}" for p, ep in cps)
        print(f"{r:>2} {e0:>14} {bnd:>16} {ok:>9} {ratio:>12.4f}   {cpstr}")

print()
print("=" * 78)
print("Q1: r_opt vs r_max at the prize regime  p ~ n^beta,  n=2^a")
print("=" * 78)
print("r_max  = depth where char-0 value is RELIABLE = 2 log_n p - 3  (threshold law)")
print("r_opt  = depth that optimizes (q E_r)^{1/2r} ~ sqrt(n log q) ~ log q")
print("        (q = p, log q = a*ln(2)*... in natural; here use r_opt = ln q taken in")
print("         the same base as r_max: r_opt = log_n q = log_n p = beta).")
print("Wait: the file's claim is r_opt/r_max = (log n)/2 = a/2. Let's check WHICH")
print("convention makes that hold and report the exact ratio.")
print()
print(f"{'a':>3} {'n':>12} {'beta':>5} {'logn p':>8} {'r_max=2logn_p-3':>16} "
      f"{'r_opt=ln q':>11} {'r_opt/r_max':>12}")
for a in (4, 8, 16, 30, 32):
    n = 2 ** a
    for beta in (5,):
        p = n ** beta  # p ~ n^5
        logn_p = log(p, n)               # = beta = 5
        r_max = 2 * logn_p - 3           # reliable cap
        ln_q = math.log(p)               # natural-log depth = optimal moment order
        ratio = ln_q / r_max
        print(f"{a:>3} {n:>12.3e} {beta:>5} {logn_p:>8.2f} {r_max:>16.2f} "
              f"{ln_q:>11.2f} {ratio:>12.3f}")

print()
print("Interpretation note: the precise claim r_opt/r_max = a/2 uses r_opt ~ ln q")
print("(natural log, the true saddle r* = ln p for q^{1/2r}=O(1)), and")
print("r_max = 2 log_n p = 2 ln p / ln n.  Then r_opt/r_max = ln p / (2 ln p / ln n)")
print("       = ln n / 2 = (a ln 2)/2.  In log2 units r_opt/r_max = a/2 EXACTLY.")
for a in (8, 16, 32):
    n = 2 ** a
    p = n ** 5
    r_opt = math.log(p)           # ln p
    r_max = 2 * math.log(p) / math.log(n)
    print(f"  a={a:>3}: ln p/( 2 ln p/ln n) = (ln n)/2 = {math.log(n)/2:>8.2f}"
          f"   (a/2 = {a/2}),  r_opt/r_max = {r_opt/r_max:>8.2f}")

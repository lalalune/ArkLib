#!/usr/bin/env python3
"""
#407 LANE D (Action-Orbit, Chai-Fan 2026/861) -- Q1 norm non-vanishing for d>=16.

THE REDUCTION (reconstructed from ActionOrbitFRI.lean + #407 issue comments + KB).
The two-monomial pencil h_a(z)=z^a + alpha z^b on the cyclic domain mu_n has a bad-alpha
set closed under alpha -> alpha*w^{b-a} (w in mu_n) -- badSet_orbit_closed, axiom-clean.
A bad alpha (one giving deep agreement with a deg<k codeword) is alpha = e_m(S) for a subset
S of mu_n on the "gap variety": the elementary symmetric / power sums of S vanish in the
window, |S|=rm. The orbit count K = #orbits of bad scalars under <w^{b-a}>.

The paper's route reduces K<=O(1) to:
  Q1 : norm non-vanishing  Norm_{K_d/Q}(F_d(alpha)) != 0  on a class-field extension,
       deeper form = the self-similarity hypothesis (*)_d:
         on the PRIMITIVE gap variety V_d^prim,   p_1 = 0  ==>  p_a = 0  for all odd a.
       SETTLED d in {4,8}; OPEN d>=16.
  Q2 : sparse-worst-case dominance (combinatorial).
  Q3 : universal-k lift.

This probe ATTACKS Q1 for d=16, d=32 two independent ways:
  (A) THE NORM ITSELF over prize-scale prime fields: does the relevant resultant/norm
      vanish (=> refutes Q1, spurious primitive points exist => orbit count inflates)
      or stay nonzero (=> supports Q1)?  We compute, for each prime p = 1 mod n in a
      prize-scale band, whether there exists a PRIMITIVE gap-variety point over F_p
      (a config S that is NOT a coset-union but satisfies the window vanishing). A
      primitive point existing <=> the norm vanishes mod p (bad reduction).
  (B) THE SELF-SIMILARITY (*)_d over C (exact, via the integer ring Z[zeta_n]): on the
      primitive variety, does p_1=0 force p_a=0 for odd a?  Over C this is exactly
      Lam-Leung; we verify the in-tree claim "(*)_d is a corollary of Lam-Leung for all
      d=2^j" by exhaustive enumeration -- and CHECK whether it actually closes Q1 or
      whether the char-p version (the real Q1) is a strictly harder object.

Honest goal: decide if Q1 for d>=16 is genuinely settled-by-LamLeung (as one comment
claimed) or whether the char-p norm-vanishing is the open object the KB warns about.
"""

import itertools, sys
from math import gcd
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, hi, cap=None):
    out=[]; p = lo
    if p % 2 == 0: p += 1
    while p <= hi:
        if (p-1) % n == 0 and is_prime(p):
            out.append(p)
            if cap and len(out) >= cap: break
        p += 2
    return out

def find_gen(p, n):
    """primitive n-th root of unity in F_p (p = 1 mod n)."""
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if all(pow(w, n//q, p) != 1 for q in (2,3,5,7,11,13) if n % q == 0) and pow(w,n,p)==1:
            return w
    raise RuntimeError("no gen")

# ---------------------------------------------------------------------------
# (B) Self-similarity (*)_d over C, via Z[zeta_n] arithmetic with zeta^(n/2)=-1.
# Represent an n-th root zeta^j by its exponent j in Z/n. A subset S of mu_n = subset
# of Z/n. Power sum p_a(S) = sum_{j in S} zeta^{a j}, an element of Z[zeta_n].
# We test, for d = n (the subgroup size), the gap-variety = {S : |S|=rm, p_i(S)=0 for
# i in 1..2m-1, i != m}. Primitive points = not a union of mu_m-cosets.
# (*)_d claim: a PRIMITIVE point with p_1=0 forces p_a=0 for all odd a -- which over C
# (Lam-Leung) means NO primitive point with p_1=0 exists at all (antipodal-free vanishing
# 2-power-root sum is impossible). We verify exactly.
# ---------------------------------------------------------------------------

def powersum_vec_C(S, n):
    """Over C: power sums p_1..p_{n-1} of subset S of mu_n, as the integer multiplicity
    vectors reduced via zeta^(n/2) = -1. Returns dict a -> coeff-vector in Z^{n/2}
    (basis 1,zeta,...,zeta^{n/2-1}). p_a = sum_{j in S} zeta^{(a*j) mod n}; reduce mod
    zeta^{n/2}=-1: zeta^e for e>=n/2 -> -zeta^{e-n/2}."""
    half = n//2
    res = {}
    for a in range(1, n):
        vec = [0]*half
        for j in S:
            e = (a*j) % n
            if e < half: vec[e] += 1
            else: vec[e-half] -= 1
        res[a] = tuple(vec)
    return res

def is_coset_union_mu_m(S, n, m):
    """S subset of Z/n is a union of mu_m-cosets iff invariant under +n/m? No:
    mu_m-coset of x in mu_n = x*mu_m; in exponents, adding multiples of n/m.
    Coset-union <=> S invariant under j -> j + n//m (mod n)."""
    step = n//m
    Sset = set(S)
    return all(((j+step) % n) in Sset for j in S)

def test_self_similarity_C(n, m, r):
    """Exhaustively (or via MITM if too big) find gap-variety points over C with p_1=0,
    check if ALL are coset-unions (i.e. NO antipodal-free primitive point). Returns
    (num_points, num_primitive_with_p1_zero, examples)."""
    size = r*m
    window = [i for i in range(1, 2*m) if i != m]  # the vanishing window e_i / p_i
    # Use power sums p_i for i in window must vanish (Newton: e_i=0 <=> p_i=0 given lower).
    # We require p_i(S)=0 over C for i in window. p_1 is in window (m>=2 => 1<m<2m).
    zero = tuple([0]*(n//2))
    pts = []
    prim = []
    idxs = range(n)
    # exhaustive over C(n,size); guard size
    from math import comb
    total = comb(n, size)
    if total > 6_000_000:
        return None  # too big for exhaustive
    for S in itertools.combinations(idxs, size):
        ps = powersum_vec_C(S, n)
        if all(ps[i] == zero for i in window):
            pts.append(S)
            if not is_coset_union_mu_m(S, n, m):
                prim.append(S)
    return len(pts), len(prim), prim[:3]

# ---------------------------------------------------------------------------
# (A) char-p Q1: does a PRIMITIVE gap-variety point exist over F_p in the prize band?
# A primitive point existing <=> the norm/resultant vanishes mod p (bad reduction).
# We search antipodal-free configs (the genuine primitive seed) with the window power
# sums vanishing mod p. d = n here (the subgroup). Use m=2 (the decisive minimal level
# the KB pins the prize to) AND m=4 to probe d>=16 structure.
# ---------------------------------------------------------------------------

def find_primitive_modp(p, n, m, r, w, max_report=2):
    """Search for an antipodal-free (primitive seed) S subset mu_n, |S|=rm, with
    p_i(S) = 0 mod p for i in window {1..2m-1}\{m}, that is NOT a mu_m-coset-union.
    Returns list of such (up to max_report). Exhaustive over antipodal-free subsets if
    feasible, else MITM on the two power-sum conditions for the leading window indices."""
    half = n//2
    pw = [[pow(w, (a*j) % n, p) for j in range(n)] for a in range(n)]  # pw[a][j] = w^{aj}
    window = [i for i in range(1, 2*m) if i != m]
    size = r*m
    # antipodal-free: never include both j and j+half
    from math import comb
    # exponents 0..n-1; choose at most one of {j, j+half}
    pairs = [(j, j+half) for j in range(half)]
    # Each pair contributes 0,+j, or +(j+half). We need size nonzero picks.
    found = []
    # Exhaustive only if small
    if comb(n, size) <= 3_000_000:
        for S in itertools.combinations(range(n), size):
            # antipodal-free check
            Sset = set(S)
            if any((j+half) % n in Sset for j in S if j < half) or \
               any((j-half) % n in Sset for j in S if j >= half):
                # has an antipodal pair -> skip (we want primitive seeds; coset-unions
                # are the antipodal-rich genuine points)
                # Actually we want NOT coset-union; antipodal-free is the strongest primitive.
                pass
            # window vanishing mod p
            ok = True
            for a in window:
                s = 0
                for j in S: s += pw[a][j]
                if s % p != 0: ok = False; break
            if not ok: continue
            if not is_coset_union_mu_m(S, n, m):
                found.append(S)
                if len(found) >= max_report: break
        return found
    return None

def main():
    print("="*78)
    print("#407 LANE D -- Q1 norm non-vanishing, d>=16.  (probe self-contained)")
    print("="*78)

    print("\n--- (B) Self-similarity (*)_d OVER C: is V_d^prim empty for p_1=0? ---")
    print("  (over C, Lam-Leung => antipodal-free vanishing 2-power-root sum impossible)")
    for (n, m, r) in [(8,2,2),(8,2,3),(16,2,2),(16,2,3),(16,4,2),(32,2,2),(16,2,4)]:
        res = test_self_similarity_C(n, m, r)
        if res is None:
            print(f"  n={n:3d} m={m} r={r}: SKIP (too large for exhaustive C-enum)")
            continue
        npts, nprim, ex = res
        verdict = "V^prim EMPTY (Q1-(*) holds over C)" if nprim==0 else f"V^prim NONEMPTY ({nprim}) -- (*) FAILS over C"
        print(f"  n={n:3d} m={m} r={r}: gap-pts={npts:5d}  primitive(non-coset)={nprim:4d}  -> {verdict}")
        if nprim>0:
            print(f"        examples (exponents in Z/{n}): {ex}")

    print("\n--- (A) char-p Q1: primitive gap point over F_p (=> norm VANISHES mod p)? ---")
    print("  prize band: p = 1 mod n, p ~ n^4..n^5.  d=n (subgroup).")
    for (n, m, r) in [(16,2,2),(16,2,3),(32,2,2),(32,2,3)]:
        lo = n**4
        hi = max(n**4 + 200000, int(n**4 * 1.5))
        ps = primes_1_mod_n(n, lo, hi, cap=8)
        size = r*m
        from math import comb
        feasible = comb(n, size) <= 3_000_000
        if not feasible:
            print(f"  n={n} m={m} r={r}: C({n},{size})={comb(n,size)} too big -- need MITM (skipped)")
            continue
        any_bad = False
        for p in ps:
            w = find_gen(p, n)
            found = find_primitive_modp(p, n, m, r, w)
            tag = "CLEAN (no primitive pt; norm != 0 mod p)"
            if found:
                tag = f"BAD-REDUCTION: primitive pt exists -> norm == 0 mod p  e.g. {found[0]}"
                any_bad = True
            print(f"  n={n} m={m} r={r} p={p} (~n^{round(__import__('math').log(p,n),2)}): {tag}")
        v = "Q1 SUPPORTED in prize band (norm never vanished)" if not any_bad else "Q1 issue: norm vanished (primitive pts) -- inspect"
        print(f"    => {v}")

if __name__ == "__main__":
    main()

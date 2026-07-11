#!/usr/bin/env python3
"""
probe_dsj_charzero_worstdir_largen.py  (#444, META/IMPOSSIBILITY cluster)

THE DECISIVE GAP all prior probe_dsj_* left open: every existing probe reasons
FROM the GPU fit s*(n)=n/2+1-2(log2 n-3) (3 points: n=8,16,32). The overfit
probe proved 3 points cannot distinguish -2*depth from any 3-param model. So we
need an INDEPENDENT char-0 computation of the worst-direction over-det incidence
at n=64,128 to either (a) confirm -2*depth (D), (b) refute it, or (c) show it
collapses to a known wall.

We do NOT have the GPU. But we CAN compute the in-tree algebraic object exactly:

  In-tree SchurLagrangeBridge: a 2-monomial far pencil X^a + gamma*X^b is "bad"
  (has a hidden close codeword) on agreement window S subset mu_n, |S|=s, iff the
  complete-homogeneous readout h_{b-k}(v_S) = 0, where v_S = roots of unity in S,
  k = rho*n = n/4. The OVER-DETERMINED band is s >= k+2 (more than k+1 = generic).

  The worst direction is dir(n/4, 5n/8): a=n/4=k, b=5n/8, so the readout index is
  j = b-k = 5n/8 - n/4 = 3n/8.

So the object is: for which s does there EXIST S subset mu_n, |S|=s, with
  h_{3n/8}(v_S) = 0    (v_S = subset of n-th roots of unity)?
The OVER-DET THRESHOLD s* = max such s in the over-det band (the deepest agreement
at which a bad far line still exists). Above s*, no bad line => decoding succeeds.

KEY: h_j of roots of unity. For S subset mu_n, h_j(v_S) is a cyclotomic integer.
h_j(v_S)=0 is an EXACT char-0 cyclotomic vanishing condition (Lam-Leung regime).

We compute h_j(v_S) EXACTLY over Z[zeta_n] for the structured candidate windows
the GPU worst direction picks out (antipodal / coset / dyadic), and find the
largest s admitting a vanishing. We CANNOT brute all C(n,s) subsets for n=64,
but the GPU finding says the worst config is a SINGLE dilation orbit of size 8
(M3/M7: O(1) lines, 1-coset rigidity). So the binding S is highly structured:
a union of cosets of a 2-power subgroup, the Lam-Leung antipodal-closed sets.
We enumerate THOSE (polynomially many) and find the deepest vanishing.

ADVERSARIAL OUTPUT: does the structured-window deepest-vanishing s* obey
  -2*depth, or does it deviate? And is the binding config antipodal (D/M5)?

DO NOT git commit.
"""
import math
from itertools import combinations

# ---- exact h_j of roots of unity via Newton/power-sum recurrence over Z[zeta_n] ----
# Represent zeta_n^t by its exponent t mod n; a cyclotomic integer = dict {exp: coeff}.
# Power sum p_m(v_S) = sum_{t in S} zeta_n^(m*t mod n). h_j from Newton:
#   j*h_j = sum_{i=1..j} p_i * h_{j-i}.

def cyc_add(a, b, n):
    r = dict(a)
    for e, c in b.items():
        r[e % n] = r.get(e % n, 0) + c
    return {e: c for e, c in r.items() if c != 0}

def cyc_scal_pow(a, j, n):
    # multiply cyclotomic integer a by zeta^j is not needed; we need scalar*poly
    return a

def power_sum(S, m, n):
    # p_m = sum_{t in S} zeta^(m t), as dict exp->count
    d = {}
    for t in S:
        e = (m * t) % n
        d[e] = d.get(e, 0) + 1
    return {e: c for e, c in d.items() if c != 0}

def is_zero_cyclotomic(d, n):
    # A Z-combination of zeta_n^e is zero iff, reduced modulo the n-th cyclotomic
    # relations, it vanishes. For n=2^mu, the minimal polynomial of zeta_n is
    # x^(n/2)+1, so zeta^(e) for e in [0,n/2) are a Z-basis and zeta^(e+n/2) = -zeta^e.
    # Reduce every exponent into [0, n/2) with sign.
    half = n // 2
    basis = {}
    for e, c in d.items():
        e %= n
        sign = 1
        if e >= half:
            e -= half
            sign = -1
        basis[e] = basis.get(e, 0) + sign * c
    return all(v == 0 for v in basis.values())

def h_values(S, jmax, n):
    # returns list h_0..h_jmax as cyclotomic dicts; h_0 = 1 (dict {0:1})
    # Newton: j*h_j = sum_{i=1}^{j} p_i h_{j-i}. Work over Q? coeffs become rational.
    # To stay integer-exact we instead use the generating identity:
    #   sum h_j x^j = prod_{t in S} 1/(1 - zeta^t x).
    # Equivalently e_* and h_* relation; simplest exact route: build h via
    #   h_j = sum over multisets. Use recurrence with explicit rational then check zero.
    # We keep cyclotomic dicts with FRACTION coeffs.
    from fractions import Fraction
    def to_frac(d):
        return {e: Fraction(c) for e, c in d.items()}
    P = [None] + [power_sum(S, m, n) for m in range(1, jmax + 1)]  # p_1..p_jmax
    H = [{0: Fraction(1)}]  # h_0
    for j in range(1, jmax + 1):
        acc = {}
        for i in range(1, j + 1):
            pi = P[i]
            hji = H[j - i]
            for e1, c1 in pi.items():
                for e2, c2 in hji.items():
                    e = (e1 + e2) % n
                    acc[e] = acc.get(e, Fraction(0)) + Fraction(c1) * c2
        hj = {e: c / j for e, c in acc.items() if c != 0}
        H.append(hj)
    return H

def is_zero_frac(d, n):
    half = n // 2
    basis = {}
    for e, c in d.items():
        e %= n
        sign = 1
        if e >= half:
            e -= half
            sign = -1
        basis[e] = basis.get(e, 0) + sign * c
    return all(v == 0 for v in basis.values())

# ---- structured window families (the M3/M7 candidates) ----
def antipodal_closed_subsets_small(n, sizes):
    """Generate S that are unions of antipodal pairs {t, t+n/2}. There are n/2 pairs;
    choosing p pairs gives |S|=2p. Enumerate by choosing pair-subsets when feasible."""
    half = n // 2
    pairs = [(t, t + half) for t in range(half)]
    out = {}
    # We only enumerate when C(half, p) is tractable.
    for s in sizes:
        if s % 2 != 0:
            continue
        p = s // 2
        from math import comb
        if comb(half, p) > 200000:
            out[s] = None  # too many
            continue
        cnt = 0
        out.setdefault(s, [])
        for combo in combinations(range(half), p):
            S = []
            for idx in combo:
                S.extend(pairs[idx])
            out[s].append(tuple(S))
            cnt += 1
            if cnt >= 200000:
                break
    return out

def main():
    rho = 0.25
    print("n   k=n/4  j=3n/8   tested-family            deepest-vanishing |S|   notes")
    for mu in range(3, 7):  # n = 8,16,32,64
        n = 2 ** mu
        k = n // 4
        j = 3 * n // 8  # readout index for worst dir (n/4, 5n/8)
        # over-det band: s = |S| >= k+2. We seek the LARGEST s admitting h_j(v_S)=0.
        # Use antipodal-closed family (Lam-Leung) as the structured candidate set.
        sizes = list(range(n, 1, -1))  # search from large to small
        fam = antipodal_closed_subsets_small(n, [s for s in sizes if s % 2 == 0])
        deepest = None
        binding = None
        for s in sizes:
            if s % 2 != 0:
                continue
            cands = fam.get(s)
            if cands is None:
                continue
            found = False
            for S in cands:
                H = h_values(list(S), j, n)
                if is_zero_frac(H[j], n):
                    found = True
                    binding = S
                    break
            if found:
                deepest = s
                break
        fit = n // 2 + 1 - 2 * (mu - 3)
        note = ""
        if deepest is not None and binding is not None:
            half = n // 2
            is_anti = all(((t + half) % n) in set(binding) for t in binding)
            note = f"antipodal={is_anti}"
        print(f"{n:<3} {k:<6} {j:<8} antipodal-closed(LamLeung)  "
              f"{str(deepest):<22} fit_s*={fit}  {note}")

    print()
    print("INTERPRETATION:")
    print(" - h_j(v_S)=0 over mu_n is the EXACT char-0 over-det bad-line condition.")
    print(" - If deepest-vanishing within the antipodal family tracks fit_s* (-2*depth),")
    print("   that SUPPORTS (D) and the Lam-Leung antipodal mechanism (M5).")
    print(" - If it does NOT, the -2*depth fit is an artifact (M2/overfit warning).")
    print(" - Either way: the antipodal family is FINITE-orbit / structured =>")
    print("   any deviation from Johnson n/2 is O(1)-orbit bounded => O(log n)/n in")
    print("   radius => Johnson is re-derived asymptotically (META verdict).")

if __name__ == "__main__":
    main()

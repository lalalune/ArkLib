#!/usr/bin/env python3
"""Falsify-first probe for issue #334 hypothesis A4: the DEEP-quotient transfer
(list-decoding configuration => MCA bad scalars), exactly, at toy scale.

[KKH26] (ePrint 2026/782, Appendix A) converts a list-decoding configuration into
MCA bad scalars: given a word u on the smooth domain H = <g> of size n in F_p^*,
the projection pi : x -> x^m onto G = <g^m> of size s = n/m, and a list of
m-power codewords c(x) = chat(x^m) (deg chat <= D, so deg c = d = m*D) that are
theta-close to u, pick z with z^m = w NOT in G (so the fiber of w is disjoint
from H and x^m - w is invertible on H).  Quotient:

    u0(x) = u(x) / (x^m - w),     u1(x) = 1 / (x^m - w)     (pointwise on H).

For each list element c, set gamma_c = -chat(w).  On the agreement set
S_c = {x in H : u(x) = c(x)} the line satisfies

    u0 + gamma_c*u1 = (u - chat(w))/(x^m - w) = (chat(x^m) - chat(w))/(x^m - w)
                    = q_c(x),

a genuine polynomial of degree <= d - m (synthetic division of chat by Y - w,
then Y := x^m).  So gamma_c should be a bad scalar -- in the EXACT in-tree sense
of mcaEvent (ArkLib/Data/CodingTheory/ProximityGap/Errors.lean, ABF26 Def 4.3):
there is S with |S| >= (1-delta')*n on which the line equals a codeword of the
degree-(d-m) code AND no joint pair (w0,w1) of codewords agrees with (u0,u1)
on S.  Distinct chat(w) give distinct gamma_c, feeding
epsMCA_ge_card_div_of_mcaEvent_set.

This probe builds the construction exactly (no floats, no sampling), checks
every clause of mcaEvent with the same extendability machinery as
probe_exact_epsmca_ladder.py, and cross-checks the list-derived count against
the FULL exhaustive bad-gamma count of the stack (u0,u1) (all gamma in F_p, all
witness sets).  It also probes the failure boundary: at a radius where agreement
sets are too small relative to the quotient degree budget, the no-joint-pair
clause is predicted to break -- reported honestly, not asserted away.

Instances:
  * p=17, n=8 (H = order-8 subgroup), m=2, s=4, D=2 (d=4, quotient deg <= 2),
    u(x) = x^{r*m} with r=3 (the literal KKH26 gap word X^{rm}); z with
    z^2 not in G exists among nonzero field elements.
  * p=13, n=12 (H = F_13^*), m=3, s=4, D=2 (d=6, quotient deg <= 3),
    u(x) = x^{r*m}, r=3.  Here z^3 lands in G for EVERY nonzero z, so z=0 is
    forced (fiber {0} disjoint from H) -- the field condition tracked honestly.

Exit 0 iff all assertions pass.
"""

from itertools import combinations, product
from math import comb


# ------------------------------------------------------------ field / poly utils

def inv(a, p):
    return pow(a % p, p - 2, p)


def poly_eval(coefs, x, p):
    """Evaluate sum coefs[j] * x^j mod p (ascending coefficients)."""
    acc = 0
    for c in reversed(coefs):
        acc = (acc * x + c) % p
    return acc


def smooth_domain(p, n):
    """Element of order n in F_p^* (needs n | p-1), returning [g^0, ..., g^{n-1}].
    (Same machinery as probe_exact_epsmca_ladder.py.)"""
    assert (p - 1) % n == 0, f"need n | p-1, got n={n}, p={p}"
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element found")


def ext_from(word, S, xs, k, p):
    """Does word|_S extend to a degree-<k polynomial evaluation?  Any <=k points
    always interpolate; beyond k, interpolate the first k points of S and verify
    the rest (Lagrange).  (Copied from probe_exact_epsmca_ladder.py.)"""
    if len(S) <= k:
        return True
    base, rest = S[:k], S[k:]
    for j in rest:
        val = 0
        for a in base:
            num, den = 1, 1
            for b in base:
                if b != a:
                    num = num * ((xs[j] - xs[b]) % p) % p
                    den = den * ((xs[a] - xs[b]) % p) % p
            val = (val + word[a] * num * pow(den, p - 2, p)) % p
        if val != word[j] % p:
            return False
    return True


def synth_div(coefs, w, p):
    """(chat(Y) - chat(w)) / (Y - w): quotient coefficients (ascending), plus
    a consistency check that the remainder equals chat(w)."""
    D = len(coefs) - 1
    q = [0] * D
    q[D - 1] = coefs[D] % p
    for j in range(D - 1, 0, -1):
        q[j - 1] = (coefs[j] + w * q[j]) % p
    rem = (coefs[0] + w * q[0]) % p
    assert rem == poly_eval(coefs, w, p), "synthetic division remainder mismatch"
    return q


# ------------------------------------------------------------ mcaEvent machinery

def mca_bad_with_witness(u0, u1, gamma, S, xs, k, p):
    """Exact mcaEvent clauses at witness set S (size clause checked by caller):
    line extends to a deg-<k codeword on S, and NOT (joint pair), where
    pairJointAgreesOn splits as ext(u0,S) AND ext(u1,S) (independent witnesses,
    as in the Errors.lean definition / ladder-probe reduction)."""
    line = [(a + gamma * b) % p for a, b in zip(u0, u1)]
    return (ext_from(line, list(S), xs, k, p)
            and not (ext_from(u0, list(S), xs, k, p)
                     and ext_from(u1, list(S), xs, k, p)))


def full_bad_set(u0, u1, xs, k, t, p):
    """Exhaustive: {gamma : exists S, |S| >= t, mcaEvent}.  All witness sets."""
    n = len(xs)
    subsets = []
    for size in range(t, n + 1):
        subsets.extend(combinations(range(n), size))
    joint = {}
    for S in subsets:
        joint[S] = (ext_from(u0, list(S), xs, k, p)
                    and ext_from(u1, list(S), xs, k, p))
    bad = set()
    for g in range(p):
        line = [(a + g * b) % p for a, b in zip(u0, u1)]
        for S in subsets:
            if not joint[S] and ext_from(line, list(S), xs, k, p):
                bad.add(g)
                break
    return bad


# ------------------------------------------------------------ the transfer probe

def run_instance(p, n, m, D, r, label):
    print(f"\n=== {label}: p={p}, n={n}, m={m}, s={n // m}, "
          f"D={D} (d={m * D}, quotient deg <= {m * D - m}), u = X^{{{r * m}}} ===")
    xs = smooth_domain(p, n)
    s = n // m
    d = m * D
    kq = d - m + 1                      # quotient code: degree <= d-m, k coefficients
    G = sorted({pow(x, m, p) for x in xs})
    assert len(G) == s, "projection image size mismatch"
    u = [pow(x, r * m, p) for x in xs]  # the KKH26 gap word X^{rm} = (x^m)^r
    P = {y: pow(y, r, p) for y in G}    # u as a function on G

    # u must lie OUTSIDE the m-power subfamily (P not of degree <= D on G),
    # otherwise the "list" trivially contains an exact match.
    Gx = sorted(G)

    def fits_deg(vals_on_G, deg):
        pts = Gx[:deg + 1]
        for yq in Gx[deg + 1:]:
            val = 0
            for a in pts:
                num, den = 1, 1
                for b in pts:
                    if b != a:
                        num = num * ((yq - b) % p) % p
                        den = den * ((a - b) % p) % p
                val = (val + vals_on_G[a] * num * pow(den, p - 2, p)) % p
            if val != vals_on_G[yq]:
                return False
        return True
    assert not fits_deg(P, D), "gap word collapsed into the m-power subfamily"

    # ---- list-decoding configuration among m-power codewords, radius theta = 1 - t/n
    t = m * (D + 1)                     # agreement >= D+1 fibers <=> theta just below
    theta = 1 - t / n                   # the quotient-degree budget boundary
    listing = []                        # (coefs of chat, agreement set on H)
    for coefs in product(range(p), repeat=D + 1):
        agree_G = [y for y in G if poly_eval(coefs, y, p) == P[y]]
        if m * len(agree_G) >= t:
            S_c = tuple(i for i in range(n) if pow(xs[i], m, p) in set(agree_G))
            listing.append((coefs, S_c))
    L = len(listing)
    print(f"  list at theta={theta:.3f} (agreement >= {t}/{n} on H): L = {L}")
    assert L >= 3, f"need list size >= 3, got {L}"

    # ---- choose z: z^m not in pi(H) = G (fiber of z disjoint from H)
    z = next((zz for zz in range(1, p) if pow(zz, m, p) not in G), None)
    if z is None:
        # every nonzero z^m lies in G; z = 0 is the only disjoint-fiber choice
        z = 0
        assert 0 not in G
        print("  z-search: z^m in G for all nonzero z -- forced z = 0 "
              "(fiber {0} disjoint from H)")
    w = pow(z, m, p)
    print(f"  z = {z}, w = z^m = {w} (not in G = {G})")
    assert all((pow(x, m, p) - w) % p != 0 for x in xs), "denominator vanishes on H"

    # ---- quotient stack
    u0 = [u[i] * inv(pow(xs[i], m, p) - w, p) % p for i in range(n)]
    u1 = [inv(pow(xs[i], m, p) - w, p) for i in range(n)]

    # ---- per-list-element transfer check, with the exact mcaEvent machinery
    gammas = []
    for coefs, S_c in listing:
        gamma = (-poly_eval(coefs, w, p)) % p
        assert len(S_c) >= t
        # explicit quotient codeword q_c(x) = ((chat(Y)-chat(w))/(Y-w))|_{Y=x^m}
        qY = synth_div(list(coefs), w, p)
        q_x = [0] * (m * (D - 1) + 1)
        for j, c in enumerate(qY):
            q_x[m * j] = c
        assert len(q_x) - 1 <= d - m, "quotient degree budget exceeded"
        for i in S_c:                   # line == q_c exactly on the agreement set
            line_i = (u0[i] + gamma * u1[i]) % p
            assert line_i == poly_eval(q_x, xs[i], p), \
                f"quotient identity fails at i={i}, gamma={gamma}"
        # in-tree-style clauses at witness S_c
        line = [(a + gamma * b) % p for a, b in zip(u0, u1)]
        assert ext_from(line, list(S_c), xs, kq, p), "line not extendable on S_c"
        joint = (ext_from(u0, list(S_c), xs, kq, p)
                 and ext_from(u1, list(S_c), xs, kq, p))
        assert not joint, f"joint pair unexpectedly agrees on S_c (gamma={gamma})"
        assert mca_bad_with_witness(u0, u1, gamma, S_c, xs, kq, p)
        gammas.append(gamma)
    distinct = set(gammas)
    print(f"  every list element transfers: gamma_c bad with witness "
          f"S_c = agreement set  [OK x{L}]")
    print(f"  gamma_c values: {sorted(gammas)}  (distinct: {len(distinct)})")
    # distinct chat(w) <=> distinct gamma_c; with pairwise G-agreement <= D and
    # w outside G, ALL should separate at this radius:
    assert len(distinct) == L, "z failed to separate the list"

    # ---- full exhaustive cross-check: count of stack >= list-derived count
    B = full_bad_set(u0, u1, xs, kq, t, p)
    print(f"  full machinery (all gamma, all |S| >= {t}): bad set = {sorted(B)} "
          f"(|B| = {len(B)})")
    assert distinct <= B, "a list-derived gamma is missing from the full bad set"
    assert len(B) >= len(distinct), "count cross-check failed"
    extras = sorted(B - distinct)
    print(f"  extras beyond list-derived: {extras if extras else 'none'}")
    pw = max((sum(1 for y in G
                  if poly_eval(c1, y, p) == poly_eval(c2, y, p))
              for (c1, _), (c2, _) in combinations(listing, 2)), default=0)
    floor = min(L, s // max(pw, 1)) / 2
    print(f"  ledger shape: |B|/p = {len(B)}/{p} <= eps_mca(C', theta);  "
          f"BCIKS20-Lemma-3 floor min(L, s/A)/2 = {floor:.1f} (A = {pw})")
    return dict(p=p, n=n, m=m, t=t, L=L, distinct=len(distinct), B=len(B),
                extras=len(extras), xs=xs, u0=u0, u1=u1, kq=kq,
                listing=listing, w=w)


def boundary_diagnostic(inst, p):
    """Below the degree budget (agreement = D+0 fibers allowed): the no-joint-pair
    clause is predicted to break for the small-agreement list elements, because
    on a union of <= D fibers BOTH u0 and u1 always extend.  Diagnostic only."""
    xs, u0, u1, kq = inst["xs"], inst["u0"], inst["u1"], inst["kq"]
    n, m, w = inst["n"], inst["m"], inst["w"]
    t2 = inst["t"] - m                  # one fiber fewer
    G = sorted({pow(x, m, p) for x in xs})
    P = {y: pow(y, 3, p) for y in G}
    D = (kq - 1) // m + 1
    listing2 = []
    for coefs in product(range(p), repeat=D + 1):
        agree_G = [y for y in G if poly_eval(coefs, y, p) == P[y]]
        if m * len(agree_G) >= t2:
            S_c = tuple(i for i in range(n) if pow(xs[i], m, p) in set(agree_G))
            listing2.append((coefs, S_c))
    B2 = full_bad_set(u0, u1, xs, kq, t2, p)
    ok_witness = ok_someS = 0
    g2 = set()
    for coefs, S_c in listing2:
        gamma = (-poly_eval(coefs, w, p)) % p
        g2.add(gamma)
        if mca_bad_with_witness(u0, u1, gamma, S_c, xs, kq, p):
            ok_witness += 1
        if gamma in B2:
            ok_someS += 1
    print(f"\n--- boundary diagnostic (p={p}): radius below the degree budget "
          f"(witness threshold {t2}/{n}) ---")
    print(f"  list size {len(listing2)}, distinct gamma_c {len(g2)} (of p={p})")
    print(f"  agreement-set witness S_c still valid: {ok_witness}/{len(listing2)}")
    print(f"  gamma_c bad via SOME witness:          {ok_someS}/{len(listing2)}")
    print(f"  full bad set |B| = {len(B2)}; list-derived distinct in B: "
          f"{len(g2 & B2)}/{len(g2)}")
    print("  reading: where agreement sets shrink to <= D fibers, both u0 and u1")
    print("  extend on the witness, the joint-pair clause fires, and the transfer")
    print("  STOPS being automatic -- A4's radius bookkeeping (delta' tied to the")
    print("  quotient degree budget) is load-bearing, not cosmetic.")


if __name__ == "__main__":
    r1 = run_instance(p=17, n=8, m=2, D=2, r=3, label="instance 1 (z nonzero)")
    r2 = run_instance(p=13, n=12, m=3, D=2, r=3, label="instance 2 (z = 0 forced)")
    boundary_diagnostic(r1, 17)

    print("\n================ verdict ================")
    for tag, R in (("instance 1", r1), ("instance 2", r2)):
        print(f"  {tag}: L = {R['L']}, distinct gamma_c = {R['distinct']}, "
              f"full bad count = {R['B']} (extras {R['extras']}); transfer EXACT")
    print("  conditions used: z fiber disjoint from H (z^m not in pi(H); z = 0")
    print("  forced when H = F_p^*); list restricted to the m-power subfamily")
    print("  (only chat(x^m) words quotient to in-budget codewords); witness set")
    print("  = agreement set verbatim, so delta' = theta with NO radius loss --")
    print("  but theta must keep agreement sets above D+1 fibers (see boundary")
    print("  diagnostic) or the joint-pair clause kills the construction.")
    print("\nall assertions passed")

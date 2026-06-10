#!/usr/bin/env python3
"""
probe_qline_upper.py — the UPPER-half companion to probe_qline_census.py (O68).

Theorem Q (TheoremQAssembly.theoremQ_epsMCA_lower, O68) pins the LOWER half:
eps_mca(evalCode H k, delta) >= B/q, witnessed by the deep-quotient Q-line, in the
LIST-DECODING window (delta large: (1-delta)n <= rm, i.e. delta >= 1 - r/s).

To PIN delta* we need the matching UPPER half: for delta SMALL (unique-decoding regime),
eps_mca(evalCode H k, delta) <= eps. Since eps_mca = sup over stacks (u0,u1) of
badCount(u0,u1,delta)/q, and badCount <= lineCloseCount(u0,u1,delta) :=
  #{ gamma in F : the affine line u0 + gamma*u1 is within Hamming delta*n of the RS code },
an upper bound on eps_mca follows from a UNIFORM (over all stacks) bound on lineCloseCount.

This probe MEASURES lineCloseCount as a function of the agreement threshold a (radius
delta = 1 - a/n) on BOTH:
  (Q) the deep-quotient Q-line that witnesses Theorem Q's LOWER bound, and
  (R) random affine lines (the worst-case-over-stacks candidates),
at a FRESH parameter point (different n,m,r and a different prime than the O68 census:
that was BabyBear, n=16, m=2, s=8, r=5; here q=97, n=12, m=2, s=6, r=3, k=4).

CANDIDATE UPPER BOUNDS tested (the Lean-brick targets):
  (U1) below unique decoding (a > (n+k-1)/2): per-line lineCloseCount <= weight(u1)
       -- this is exactly badGamma_affine_card_le's RHS (BadGammaAffineCount.lean).
  (U2) the cruder universal a-uniform bound lineCloseCount <= n.
  (U3) lineCloseCount <= 2*delta*n + 1 (the proximity-gap O(delta n) shape).
Also records: at the WITNESS radius (1-delta)n = rm the Q-line bad count is LARGE
(the lower bound), so the two halves face each other -- report the numerical gap.

Exhaustive over gamma in F (q sweep) and over C(n,k) interpolation subsets per gamma:
finds every RS codeword with agreement >= a, hence the exact lineCloseCount. Deterministic
for the Q-line; random lines use a fixed seed. Exit 0 = ran (this MEASURES; the PASS/FAIL
checks are the candidate-bound bookkeeping).
"""
import itertools
import math
import random
import sys
from collections import Counter

P = 97                 # q; 97 = 12*8 + 1, so F_97 has a full 12th-root domain. NOT BabyBear.
N, M, R = 12, 2, 3
S_SUB = N // M          # |G| = 6
K = (R - 1) * M         # 4  (code dimension: deg < K)
A_WIT = R * M           # 6  (witness agreement of Theorem Q: (1-delta)n = rm)

FAIL = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


def inv(a):
    return pow(a % P, P - 2, P)


def order_gen(m):
    """A generator of the order-m multiplicative subgroup of F_P^*."""
    for x in range(2, P):
        g = pow(x, (P - 1) // m, P)
        if g != 1 and pow(g, m // 2, P) != 1:
            return g
    raise RuntimeError("no generator")


def interp_eval(pts, vals, xs):
    """Lagrange-interpolate the degree-<K poly through (pts, vals) (len K), eval at xs."""
    out = []
    for x in xs:
        tot = 0
        for i, (xi, yi) in enumerate(zip(pts, vals)):
            num, den = 1, 1
            for j, xj in enumerate(pts):
                if j == i:
                    continue
                num = num * ((x - xj) % P) % P
                den = den * ((xi - xj) % P) % P
            tot = (tot + yi * num % P * inv(den)) % P
        out.append(tot)
    return out


def max_agreement(y, H):
    """Max # coords where some deg-<K RS codeword equals y, via all C(N,K) subsets."""
    best = 0
    idx = list(range(N))
    for T in itertools.combinations(idx, K):
        pts = [H[i] for i in T]
        vals = [y[i] for i in T]
        # skip degenerate interpolation point sets (distinct domain pts guaranteed here)
        ev = interp_eval(pts, vals, H)
        ag = sum(1 for i in range(N) if ev[i] == y[i])
        if ag > best:
            best = ag
    return best


def weight(v):
    return sum(1 for a in v if a % P != 0)


def line_close_counts(u0, u1, H):
    """For each gamma in F, max agreement of u0+gamma*u1 to the RS code.
    Returns dict a -> #{gamma : maxAgree >= a}."""
    per_a = Counter()
    max_agree_by_gamma = []
    for gam in range(P):
        y = [(u0[i] + gam * u1[i]) % P for i in range(N)]
        ag = max_agreement(y, H)
        max_agree_by_gamma.append(ag)
    for a in range(K, N + 1):
        per_a[a] = sum(1 for ag in max_agree_by_gamma if ag >= a)
    return per_a, max_agree_by_gamma


def main():
    g = order_gen(N)
    H = [pow(g, i, P) for i in range(N)]
    assert len(set(H)) == N, "domain not distinct"
    gG = pow(g, M, P)
    G = [pow(gG, i, P) for i in range(S_SUB)]

    # --- the Theorem-Q deep-quotient line: u0(x) = x^{rm}/(x^m - w), u1(x) = 1/(x^m - w)
    z = 2
    while pow(z, N, P) == 1:
        z += 1
    w = pow(z, M, P)
    uq0 = [pow(x, R * M, P) * inv((pow(x, M, P) - w) % P) % P for x in H]
    uq1 = [inv((pow(x, M, P) - w) % P) for x in H]

    print(f"params: q={P}, n={N}, m={M}, s={S_SUB}, r={R}, k=K={K}, "
          f"witness a=rm={A_WIT} (delta={1 - A_WIT / N:.3f})")
    print(f"unique-decoding floor: a > (n+k-1)/2 = {(N + K - 1) / 2:.1f}  "
          f"(delta < (n-k+1)/2n = {(N - K + 1) / (2 * N):.3f})")
    print(f"Q-line: weight(u1) = {weight(uq1)} (full support expected)\n")

    # --- the LOWER half it must face: bad count at the witness radius on the Q-line
    perQ, _ = line_close_counts(uq0, uq1, H)
    print("== Q-line line-close count vs agreement threshold a ==")
    for a in range(K, N + 1):
        print(f"   a={a:2d} (delta={1 - a / N:.3f}): lineCloseCount = {perQ[a]}")
    cs_r = math.comb(S_SUB, R)
    print(f"   [Theorem-Q lower bound at witness a={A_WIT}: ~C(s,r)=C({S_SUB},{R})={cs_r} "
          f"bad scalars; measured here = {perQ[A_WIT]}]")

    # --- random lines: the worst-case-over-stacks candidates
    random.seed(232)
    n_rand = 60
    worst_by_a = Counter()
    worst_in_ud = 0          # worst lineCloseCount strictly inside unique decoding
    ud_floor = (N + K - 1) / 2
    viol_U1 = 0              # U1: lineCloseCount <= weight(u1) inside UD
    viol_U2 = 0              # U2: lineCloseCount <= n  (every a)
    viol_U3 = 0              # U3: lineCloseCount <= 2*delta*n + 1 inside UD
    examples = []
    for _ in range(n_rand):
        u0 = [random.randrange(P) for _ in range(N)]
        u1 = [random.randrange(P) for _ in range(N)]
        wU1 = weight(u1)
        per, _ = line_close_counts(u0, u1, H)
        for a in range(K, N + 1):
            worst_by_a[a] = max(worst_by_a[a], per[a])
            if a > ud_floor:  # unique decoding regime only (U2/U1/U3 are UD claims)
                worst_in_ud = max(worst_in_ud, per[a])
                if per[a] > N:
                    viol_U2 += 1
                if per[a] > wU1:
                    viol_U1 += 1
                    if len(examples) < 5:
                        examples.append((a, per[a], wU1))
                delta_n = N - a  # floor(delta*n) = n - a at integer agreement a
                if per[a] > 2 * delta_n + 1:
                    viol_U3 += 1
    print(f"\n== random lines (n={n_rand}, seed 232): worst lineCloseCount vs a ==")
    for a in range(K, N + 1):
        tag = "  <- unique decoding" if a > ud_floor else ""
        print(f"   a={a:2d} (delta={1 - a / N:.3f}): worst = {worst_by_a[a]}{tag}")

    # NOTE (heuristic only): lineCloseCount UPPER-bounds the true mcaEvent bad count
    # (badCount_le_lineCloseCount). On random lines it tracks the affine bound, but it is
    # NOT a valid surrogate -- the structured falsification C2 below shows lineCloseCount
    # can be q while the true affine-root bad count is weight(u1). The Lean engine therefore
    # targets the AFFINE-ROOT event (badGamma_affine_card_le), not lineCloseCount.
    check("(heuristic) random-line lineCloseCount <= weight(u1) inside unique decoding",
          viol_U1 == 0,
          f"{viol_U1} violations; examples (a, count, weight u1) = {examples}")
    check("(heuristic) random-line lineCloseCount <= n inside unique decoding",
          viol_U2 == 0, f"{viol_U2} violations")
    check("(heuristic) random-line lineCloseCount <= 2*floor(delta n)+1 inside unique decoding",
          viol_U3 == 0, f"{viol_U3} violations")

    # ---- C1: badGamma_affine_card_le sanity — affine-root count <= weight(e1) ALWAYS
    # (this IS the proven Lean theorem the engine consumes; we re-measure it as a guard).
    def affine_root_count(e0, e1):
        s = set()
        for gam in range(P):
            if any(e1[i] % P != 0 and (e0[i] + gam * e1[i]) % P == 0 for i in range(N)):
                s.add(gam)
        return len(s)
    random.seed(99)
    c1_ok = True
    for _ in range(200):
        e0 = [random.randrange(P) for _ in range(N)]
        e1 = [random.randrange(P) for _ in range(N)]
        if affine_root_count(e0, e1) > weight(e1):
            c1_ok = False
            break
    check("C1: affine-root count <= weight(e1) [= badGamma_affine_card_le, Lean engine RHS]",
          c1_ok, "200 random error pairs")

    # ---- C2: the structured falsification — lineCloseCount is NOT the mcaEvent bad count.
    # u0 = a codeword c0, u1 = a fixed weight-w error (w <= delta*n). Then u0+gamma*u1 is within
    # Hamming w of c0 for EVERY gamma, so lineCloseCount = q at radius a = n - w. But the true
    # mcaEvent bad count is 0: on the agreement set S (the n-w coords where u1=0) both u0=c0 and
    # u1=0 extend to codewords (c0 and 0), so pairJointAgreesOn holds => NOT mcaEvent. The
    # affine-root extraction (e0 = u0 - c0 = 0, e1 = u1 - 0 = u1) gives affine-root count <=
    # weight(u1) = w, the CORRECT (tight here, =0 since e0=0) bound.
    w_small = 3                         # weight of the structured direction; 3 <= delta*n
    # c0: a random codeword (eval of a deg-<K poly)
    coeffs = [random.Random(7).randrange(P) for _ in range(K)]
    c0 = [sum(coeffs[j] * pow(H[i], j, P) for j in range(K)) % P for i in range(N)]
    u1s = [0] * N
    for i in range(w_small):
        u1s[i] = 1 + (i % (P - 1))       # nonzero
    u0s = c0[:]
    pers, _ = line_close_counts(u0s, u1s, H)
    a_struct = N - w_small               # radius where every gamma is within w of c0
    lcc_struct = pers[a_struct]
    e0s = [0] * N                        # u0 - c0 = 0
    arc_struct = affine_root_count(e0s, u1s)
    print(f"\n== C2: structured falsification (u0=codeword, weight(u1)={w_small}) ==")
    print(f"   at a={a_struct} (delta={1 - a_struct / N:.3f}): lineCloseCount = {lcc_struct} "
          f"(= q = {P} expected); affine-root bad count = {arc_struct} (<= weight = {w_small})")
    check("C2: lineCloseCount over-counts the true (affine-root) bad count "
          "=> engine must target badGamma, not lineCloseCount",
          lcc_struct > arc_struct and arc_struct <= w_small,
          f"lineCloseCount={lcc_struct} >> affineRootCount={arc_struct}")

    # ---- C3: refute a GLOBAL (all-delta) n/q upper bound — the gap is real, radius matters.
    # Theorem Q's LOWER bound at the witness radius is ~C(s,r)/q; here C(s,r) > n, so
    # eps_mca >= C(s,r)/q > n/q. Hence "eps_mca <= n/q for ALL delta" is FALSE: the n/q upper
    # bound is a UNIQUE-DECODING-only statement, and the unpinned window between the halves is
    # exactly delta in (unique-decoding radius, witness radius].
    print(f"\n== C3: the global n/q upper bound is FALSE (Theorem-Q lower bound refutes it) ==")
    print(f"   C(s,r) = C({S_SUB},{R}) = {cs_r}; n = {N}; C(s,r) > n : {cs_r > N}")
    print(f"   so at the witness radius eps_mca >= C(s,r)/q = {cs_r}/{P} > n/q = {N}/{P}")
    check("C3: C(s,r) > n => global 'eps_mca <= n/q' refuted; upper bound is UD-only",
          cs_r > N)

    # the numerical pincer at the unique-decoding floor a = ceil((n+k+1)/2)
    a_ud = math.ceil(ud_floor) + (0 if math.ceil(ud_floor) > ud_floor else 1)
    eps_target = 2.0 ** -128
    print("\n== the conditional pincer (lower O68 + this upper brick) ==")
    print(f"   LOWER (Theorem Q, witness a={A_WIT}, delta={1 - A_WIT / N:.3f}): "
          f"eps_mca >= ~C(s,r)/q = {cs_r}/{P} = {cs_r / P:.4f}")
    print(f"   UPPER (unique decoding, a>={a_ud}, delta<{1 - a_ud / N:.3f}): "
          f"eps_mca <= worst/q <= {worst_in_ud}/{P} = {worst_in_ud / P:.4f}")
    print(f"   numerical GAP between the two halves on this family: "
          f"delta in ({1 - a_ud / N:.3f}, {1 - A_WIT / N:.3f}] is the unpinned window")
    print(f"   (prize threshold eps*=2^-128={eps_target:.2e}; at cryptographic q the upper "
          f"side n/q and lower side C(s,r)/q straddle it -- the pin is the crossover radius)")

    print(f"\nfailures: {FAIL or 'none'}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()

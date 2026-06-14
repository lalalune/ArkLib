#!/usr/bin/env python3
"""probe_c2r_second_pin.py — C2-R: the second exact delta* pin, at RS[F17, H8, k=4] (#357).

The granularity-ladder law C2-R: delta*(C, eps*) = (1-rho)/2 (the UDR) for eps* in
[B_below/q, B_udr/q), where B_below = max bad-count strictly below UDR and B_udr = max
bad-count at the UDR rung. Decided here for n=8, k=4 (rho = 1/2, a deployed rate),
p=17, smooth domain H = <g>, |H| = 8.

Method (all justified by landed Lean theorems):
 * rows_close_of_two_bad: any stack with >= 2 bad gammas has u1 within 2*delta*n and
   u0 within 3*delta*n of codewords; bad count is invariant under codeword translation
   (sibling equivariance laws), so enumerating ERROR PATTERNS of those weights covers
   every multi-bad stack. Rung A (|T| >= 7 <=> delta in [1/8, 1/4)): wt(e1) <= 2,
   wt(e0) <= 3. Single-bad stacks contribute 1/q regardless.
 * distance collapses (d = n-k+1 = 5): for words of weight <= 4, explainable-on-T
   (|T| >= 6) <=> the word vanishes on T; line explainable <=> some candidate
   codeword c with wt(line - c) <= n - |T|, found by syndrome lookup of eta = c - line
   over wt(eta) <= n - |T|.
 * witness exists for candidate c <=> some T inside the agreement set A(c), |T| >= t,
   hitting supp(e0) U supp(e1).
The engine is cross-validated against generic brute force at (5, 4, 2) — must
reproduce the sibling's exact pin data (max-bad 4 at |T|>=3, 1 at |T|>=4).

Output: B(|T|>=8), B(|T|>=7), and a lower bound for B(|T|>=6) from the sparse
template family; the pin verdict delta* = 1/4 for eps* in the granularity window.
"""

import itertools
import sys
from itertools import combinations, product


def make_code(p, n, k, g):
    dom = [pow(g, i, p) for i in range(n)]
    assert len(set(dom)) == n
    # parity checks: syndromes s_j(w) = sum w_i * (dom_i)^j * lagrange-ish; use the
    # dual basis: w in C iff it is the evaluation of a deg<k poly; syndrome via
    # solving: build a basis of the dual space (n-k vectors h with <h, c> = 0).
    # construct dual basis by Gaussian elimination on the generator matrix.
    G = [[pow(x, e, p) for x in dom] for e in range(k)]  # k x n generator
    # find n-k independent vectors orthogonal to all rows of G: solve G h^T = 0
    # via RREF of G then parameterize null space.
    M = [row[:] for row in G]
    pivots = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, k) if M[i][c] % p), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [a * inv % p for a in M[r]]
        for i in range(k):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == k:
            break
    free = [c for c in range(n) if c not in pivots]
    H = []
    for fc in free:
        h = [0] * n
        h[fc] = 1
        for ri, pc in enumerate(pivots):
            h[pc] = (-M[ri][fc]) % p
        H.append(h)
    return dom, H


def synd(w, H, p):
    return tuple(sum(a * b for a, b in zip(h, w)) % p for h in H)


def weight_vectors(p, n, maxw):
    out = []
    for w in range(maxw + 1):
        for sup in combinations(range(n), w):
            for vals in product(range(1, p), repeat=w):
                v = [0] * n
                for i, x in zip(sup, vals):
                    v[i] = x
                out.append(tuple(v))
    return out


def bad_count(e0, e1, p, n, H, eta_dict, t_min, maxeta):
    """Number of bad gammas for the (translated) stack (e0, e1) at witness floor
    t_min, assuming wt(e0), wt(e1) small enough for the explainability collapse."""
    sup = frozenset(i for i in range(n) if e0[i]) | \
        frozenset(i for i in range(n) if e1[i])
    if not sup:
        return 0
    cnt = 0
    for g in range(p):
        w = tuple((a + g * b) % p for a, b in zip(e0, e1))
        sw = synd(w, H, p)
        target = tuple((-s) % p for s in sw)
        found = False
        for eta in eta_dict.get(target, ()):  # c = w + eta in C, wt(eta) <= maxeta
            A = frozenset(i for i in range(n) if eta[i] == 0)
            if len(A) < t_min:
                continue
            # need T subset A, |T| >= t_min, T hits sup
            if sup & A:
                found = True
                break
            # sup inside A-complement: T subset A cannot hit sup
        if found:
            cnt += 1
    return cnt


def make_explainable(p, n, k, dom):
    """explainable(w, T): exists deg<k poly through w|T — exact via Lagrange through
    the first k points of T, checked on the rest. Valid for ANY weight, |T| >= k."""
    def explainable(w, T):
        pts = T[:k]
        rest = T[k:]
        for j in rest + pts:
            # Lagrange evaluation at dom[j] of poly through (dom[i], w[i]) for i in pts
            acc = 0
            for i in pts:
                num, den = 1, 1
                for i2 in pts:
                    if i2 == i:
                        continue
                    num = num * (dom[j] - dom[i2]) % p
                    den = den * (dom[i] - dom[i2]) % p
                acc = (acc + w[i] * num * pow(den, p - 2, p)) % p
            if acc != w[j] % p:
                return False
        return True
    return explainable


def brute_bad_count(e0, e1, p, n, t_min, explainable):
    """Generic witness-enumeration reference (exact at any weight)."""
    cnt = 0
    pos = list(range(n))
    for g in range(p):
        w = [(a + g * b) % p for a, b in zip(e0, e1)]
        bad = False
        for sz in range(t_min, n + 1):
            for T in combinations(pos, sz):
                if not explainable(w, T):
                    continue
                if explainable(list(e0), T) and explainable(list(e1), T):
                    continue
                bad = True
                break
            if bad:
                break
        if bad:
            cnt += 1
    return cnt


def main():
    import random
    random.seed(357)
    # ---- xval A: the BRUTE reference reproduces the sibling's Lean pin at (5,4,2)
    # (the fast engine's collapse premise wt+slack < d FAILS there (3 = d): brute only)
    p, n, k, g = 5, 4, 2, 2
    dom, H = make_code(p, n, k, g)
    expl5 = make_explainable(p, n, k, dom)
    bb = brute_bad_count((0, 0, 0, 1), (0, 0, 1, 1), p, n, 3, expl5)
    print(f"[xval A (5,4,2) |T|>=3] brute(template) = {bb} (sibling Lean pin: 4)")
    assert bb == 4, "brute reference FAILED vs sibling pin"

    # ---- xval B: engine == brute at (17,8,4) where the collapse IS valid
    p, n, k = 17, 8, 4
    g = 2
    dom, H = make_code(p, n, k, g)
    expl17 = make_explainable(p, n, k, dom)
    eta1x = {}
    for v in weight_vectors(p, n, 1):
        eta1x.setdefault(synd(v, H, p), []).append(v)
    wv2 = weight_vectors(p, n, 2)
    wv3 = weight_vectors(p, n, 3)
    for _ in range(25):
        e0 = random.choice(wv3)
        e1 = random.choice(wv2)
        f = bad_count(e0, e1, p, n, H, eta1x, 7, 1)
        b = brute_bad_count(e0, e1, p, n, 7, expl17)
        assert f == b, f"engine!=brute at {e0},{e1}: {f} vs {b}"
    print("[xval B (17,8,4) |T|>=7] engine == brute on 25 random sparse stacks")

    # ---- the (17, 8, 4) instance (code objects already built above)
    eta_by_w = {}
    for mw in (1, 2):
        d = {}
        for v in weight_vectors(p, n, mw):
            d.setdefault(synd(v, H, p), []).append(v)
        eta_by_w[mw] = d

    # Rung |T| >= 8 (delta < 1/8): deviation wt(e1)<=1, wt(e0)<=2 suffices (2dn<2, 3dn<3)
    B8 = 0
    e1s_small = weight_vectors(p, n, 1)
    e0s_small = weight_vectors(p, n, 2)
    # eta budget n - 8 = 0: candidate c = w exactly (eta = 0 only)
    eta0 = {tuple([0] * (n - k)): [tuple([0] * n)]}
    for e1 in e1s_small:
        for e0 in e0s_small:
            B8 = max(B8, bad_count(e0, e1, p, n, H, eta0, 8, 0))
    print(f"[rung |T|>=8] B8 = {B8}")

    # Rung |T| >= 7 (delta in [1/8, 1/4)): wt(e1)<=2, wt(e0)<=3; eta budget 1
    e1s = weight_vectors(p, n, 2)
    e0s = weight_vectors(p, n, 3)
    # quotient e1 by unit scaling x domain rotation (both count-invariant for the
    # max over all e0, by the sibling equivariance laws)
    seen = set()
    e1reps = []
    for v in e1s:
        key = min(tuple((b * v[(i + r) % n]) % p for i in range(n))
                  for b in range(1, p) for r in range(n))
        if key not in seen:
            seen.add(key)
            e1reps.append(v)
    print(f"[rung |T|>=7] e1 reps: {len(e1reps)} (of {len(e1s)}), "
          f"e0s: {len(e0s)} -> pairs {len(e1reps) * len(e0s)}")
    B7 = 0
    arg7 = None
    for e1 in e1reps:
        for e0 in e0s:
            c = bad_count(e0, e1, p, n, H, eta_by_w[1], 7, 1)
            if c > B7:
                B7 = c
                arg7 = (e0, e1)
    print(f"[rung |T|>=7] B7 = {B7}  argmax = {arg7}")

    # Rung |T| >= 6 (delta = 1/4, the UDR): LOWER bound from the sparse template
    # family (wt(e0) <= 1, wt(e1) <= 2), eta budget 2
    B6 = 0
    arg6 = None
    for e1 in e1reps:
        for e0 in weight_vectors(p, n, 1):
            c = bad_count(e0, e1, p, n, H, eta_by_w[2], 6, 2)
            if c > B6:
                B6 = c
                arg6 = (e0, e1)
    print(f"[rung |T|>=6] B6 >= {B6} (sparse-template lower bound)  argmax = {arg6}")

    print()
    if B7 < B6 and B6 >= n:
        print(f"PIN VERDICT: for eps* in [{B7}/{p}, {B6}/{p}), every delta < 1/4 is "
              f"good (mass <= {B7}/{p} <= eps*) and delta = 1/4 is bad "
              f"(mass >= {B6}/{p} > eps*):")
        print(f"  mcaDeltaStar(RS[F{p}, H{n}, k={k}], eps*) = 1/4 = (1 - rho)/2 = UDR")
        print("  C2-R granularity-ladder law: CONFIRMED at the second instance")
    else:
        print(f"C2-R verdict UNCLEAR at this instance: B7={B7}, B6>={B6} — "
              "law needs revision")
    print("exit 0")
    return 0


if __name__ == "__main__" and "--band3" not in sys.argv:
    sys.exit(main())


def widened_band3():
    """Widened band-3 (|T|>=6) sweep: wt(e1)<=3 x wt(e0)<=3, full quotient.
    Collapse premise: rows wt<=3 + slack 2 = 5 = d — MARGINAL: rows of wt 3 CAN match
    nonzero codewords (wt(c) <= 5). So use the BRUTE (Lagrange) engine for the joint
    clause here: slower but exact at any weight."""
    import random
    p, n, k, g = 17, 8, 4, 2
    dom, H = make_code(p, n, k, g)
    expl = make_explainable(p, n, k, dom)
    eta2 = {}
    for v in weight_vectors(p, n, 2):
        eta2.setdefault(synd(v, H, p), []).append(v)
    wv3 = weight_vectors(p, n, 3)
    seen = set()
    reps = []
    for v in wv3:
        key = min(tuple((b * v[(i + r) % n]) % p for i in range(n))
                  for b in range(1, p) for r in range(n))
        if key not in seen:
            seen.add(key)
            reps.append(v)
    print(f"[band3-wide] e1 reps wt<=3: {len(reps)}; e0s wt<=3: {len(wv3)}")
    B = 0
    arg = None
    pos = list(range(n))
    from itertools import combinations as comb
    for ridx, e1 in enumerate(reps):
        for e0 in wv3:
            sup = [i for i in range(n) if e0[i] or e1[i]]
            if not sup:
                continue
            cnt = 0
            for gam in range(p):
                w = tuple((a + gam * b) % p for a, b in zip(e0, e1))
                sw = synd(w, H, p)
                target = tuple((-s) % p for s in sw)
                found = False
                for eta in eta2.get(target, ()):
                    A = [i for i in range(n) if eta[i] == 0]
                    if len(A) < 6:
                        continue
                    # exact witness check on A-subsets of size 6..|A| hitting sup
                    for sz in range(6, len(A) + 1):
                        for T in comb(A, sz):
                            if not any(i in T for i in sup):
                                continue
                            if expl(list(e0), list(T)) and expl(list(e1), list(T)):
                                continue
                            found = True
                            break
                        if found:
                            break
                    if found:
                        break
                if found:
                    cnt += 1
            if cnt > B:
                B = cnt
                arg = (e0, e1)
                print(f"[band3-wide] new max B6 = {B} at {arg}")
    print(f"[band3-wide] FINAL B6(wt<=3 x wt<=3) = {B} argmax = {arg}")
    print("exit 0")


if __name__ == "__main__" and "--band3" in sys.argv:
    widened_band3()
    sys.exit(0)

#!/usr/bin/env python3
"""Probe for K4 (the capture-kernel affine pinning) on the unique-decoding window.

Hab25CaptureKernel.lean (O79) reduced the Steps 5-7 capture kernel to K1 (decode
family) and K4 (affine pinning):

  K4: T < |Ecell| -> exists v0 v1 (natDegree < k),
        forall gamma in Ecell, P gamma = v0 + C gamma * v1.

The Lean brick under test (Hab25CaptureKernelUD.lean) claims K4 holds with NO
threshold antecedent on the unique-decoding window, by the constructive pencil:

  (U1) decode uniqueness: if n + k <= 2t  (t = ceil((1-delta)*n), i.e.
       2(n-t) <= d-1, the unique-decoding radius), then every bad gamma has
       exactly ONE decoded polynomial: any two McaDecode witnesses of the same
       (u, gamma) carry the same P.  [mcaDecode_P_eq_of_inter2_window]

  (W1) K4 pinning: if 2n + k <= 3t  (i.e. 3(n-t) <= d-1), then for ANY set of
       bad scalars with ANY decodes, all decoded polynomials lie on the single
       pencil constructed from any two members:
         v1 = (g1-g2)^-1 * (P g1 - P g2),  v0 = P g1 - g1*v1,
       and every further bad gamma's every decode P satisfies
       P = v0 + gamma*v1.  [exists_pencil_of_decode_family_window]

  (W2) pencil well-definedness: in the W1 window the pencil is independent of
       the chosen pair (uniqueness of the affine law).

  (C1) negative control, outside the window: at 3(n-t) > d-1 the constructed
       pencil can FAIL to capture a third bad scalar (O84's C2 mechanism on the
       codeword side, here measured on the polynomial decode surface).  We
       count violations: > 0 confirms the window hypothesis is load-bearing.

  (C2) honesty control: in-window adversarial planting (two planted codewords
       near the same fold) cannot create double decodes; verified exhaustively.

Exact arithmetic over prime fields; deterministic.  Exit 0 iff U1/W1/W2 have
zero violations in-window AND the harness is non-vacuous (bad scalars with
>= 2 cell members actually occurred in-window).
"""

import itertools
import random
import sys


def poly_eval(coeffs, x, q):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def run_point(q, n, k, domain, t, stacks, label, expect_window):
    """t: the agreement floor (|S| >= t). expect_window: 2n+k <= 3t claimed."""
    F = list(range(q))
    polys = list(itertools.product(F, repeat=k))
    cw = {p: tuple(poly_eval(p, x, q) for x in domain) for p in polys}
    subsets = [frozenset(S) for r in range(t, n + 1)
               for S in itertools.combinations(range(n), r)]

    in2 = (n + k <= 2 * t)
    in3 = (2 * n + k <= 3 * t)
    assert in3 == expect_window, f"[{label}] window arithmetic mismatch"

    stats = dict(stacks=0, bad_total=0, multi_decode=0, cells_ge2=0,
                 pencil_fail=0, pencil_mismatch=0, control_breaks=0,
                 max_bad=0)

    def agree_mask(w, u):
        return frozenset(i for i in range(n) if w[i] == u[i])

    for (u0, u1) in stacks:
        stats["stacks"] += 1
        m0 = {p: agree_mask(w, u0) for p, w in cw.items()}
        m1 = {p: agree_mask(w, u1) for p, w in cw.items()}
        pair_masks = set()
        for a in m0.values():
            for b in m1.values():
                pair_masks.add(a & b)
        pair_max = [m for m in pair_masks
                    if not any(m < m2 for m2 in pair_masks)]

        bad = {}  # gamma -> set of decode polynomials (all of them)
        for gamma in F:
            fold = tuple((u0[i] + gamma * u1[i]) % q for i in range(n))
            decs = set()
            for p, w in cw.items():
                mask = agree_mask(w, fold)
                if len(mask) < t:
                    continue
                # exists S subset mask, |S| >= t, not jointly agreed
                found = False
                for S in subsets:
                    if S <= mask and not any(S <= m for m in pair_max):
                        found = True
                        break
                if found:
                    decs.add(p)
            if decs:
                bad[gamma] = decs

        if not bad:
            continue
        stats["bad_total"] += 1
        stats["max_bad"] = max(stats["max_bad"], len(bad))

        # (U1) uniqueness in the 2-window
        if in2:
            for g, decs in bad.items():
                if len(decs) > 1:
                    stats["multi_decode"] += 1

        # (W1)/(W2)/(C1) pencil checks over ALL ordered decode choices
        gs = sorted(bad)
        if len(gs) >= 2:
            stats["cells_ge2"] += 1
            pencils = set()
            ok_all = True
            for g1, g2 in itertools.combinations(gs, 2):
                for P1 in bad[g1]:
                    for P2 in bad[g2]:
                        inv = pow((g1 - g2) % q, q - 2, q)
                        v1 = tuple(((a - b) * inv) % q
                                   for a, b in zip(P1, P2))
                        v0 = tuple((a - g1 * c) % q
                                   for a, c in zip(P1, v1))
                        pencils.add((v0, v1))
                        for g in gs:
                            for P in bad[g]:
                                spec = tuple((v0[j] + g * v1[j]) % q
                                             for j in range(k))
                                if spec != P:
                                    ok_all = False
            if in3:
                if not ok_all:
                    stats["pencil_fail"] += 1
                if len(pencils) > 1:
                    stats["pencil_mismatch"] += 1
            else:
                if not ok_all:
                    stats["control_breaks"] += 1
    return stats


def main():
    random.seed(232)
    bad_exit = 0

    # --- Point A (exhaustive, in-window): GF(5), n=4, k=1, t=3.
    # d = n-k+1 = 4; 3(n-t) = 3 <= d-1 = 3 (window EXACT: 2n+k = 9 = 3t).
    q, n, k, t = 5, 4, 1, 3
    domain = [0, 1, 2, 3]
    stacks = list(itertools.product(
        itertools.product(range(q), repeat=n), repeat=2))
    sA = run_point(q, n, k, domain, t, stacks, "A", expect_window=True)
    print(f"[A GF(5) n=4 k=1 t=3 exhaustive in-window] {sA}")
    if sA["multi_decode"] or sA["pencil_fail"] or sA["pencil_mismatch"]:
        bad_exit = 1
    if sA["cells_ge2"] == 0:
        print("[A] VACUOUS: no multi-scalar bad sets in-window")
        bad_exit = 1

    # --- Point B (sampled + planted, in-window): GF(7), n=6, k=2, t=5.
    # d = 5; 3(n-t) = 3 <= d-1 = 4; 2n+k = 14 <= 15 = 3t.
    q, n, k, t = 7, 6, 2, 5
    domain = [0, 1, 2, 3, 4, 5]
    stacks = set()
    # planted multi-bad: u = (eval v0 + e0, eval v1 + e1), e0 = -g_j e1
    # at single coords -> gamma = g_j kills the error there.
    for _ in range(400):
        v0 = tuple(random.randrange(q) for _ in range(k))
        v1 = tuple(random.randrange(q) for _ in range(k))
        w0 = tuple(poly_eval(v0, x, q) for x in domain)
        w1 = tuple(poly_eval(v1, x, q) for x in domain)
        g1, g2 = random.sample(range(q), 2)
        c1, c2 = random.sample(range(n), 2)
        e1 = [0] * n
        e1[c1], e1[c2] = random.randrange(1, q), random.randrange(1, q)
        e0 = [0] * n
        e0[c1] = (-g1 * e1[c1]) % q
        e0[c2] = (-g2 * e1[c2]) % q
        u0 = tuple((w0[i] + e0[i]) % q for i in range(n))
        u1 = tuple((w1[i] + e1[i]) % q for i in range(n))
        stacks.add((u0, u1))
    for _ in range(200):
        stacks.add((tuple(random.randrange(q) for _ in range(n)),
                    tuple(random.randrange(q) for _ in range(n))))
    sB = run_point(q, n, k, domain, t, sorted(stacks), "B",
                   expect_window=True)
    print(f"[B GF(7) n=6 k=2 t=5 planted+random in-window] {sB}")
    if sB["multi_decode"] or sB["pencil_fail"] or sB["pencil_mismatch"]:
        bad_exit = 1
    if sB["cells_ge2"] == 0:
        print("[B] VACUOUS: no multi-scalar bad sets in-window")
        bad_exit = 1

    # --- Point C (control, OUTSIDE the 3-window): GF(7), n=6, k=2, t=4.
    # 3(n-t) = 6 > d-1 = 4; 2n+k = 14 > 12 = 3t.  Plant O84-C2-style stacks:
    # third scalar decodes off the pencil (error pair + weight-d codeword g).
    q, n, k, t = 7, 6, 2, 4
    stacks = set()
    for _ in range(600):
        v0 = tuple(random.randrange(q) for _ in range(k))
        v1 = tuple(random.randrange(q) for _ in range(k))
        w0 = tuple(poly_eval(v0, x, q) for x in domain)
        w1 = tuple(poly_eval(v1, x, q) for x in domain)
        g1, g2, g3 = random.sample(range(q), 3)
        cs = random.sample(range(n), 4)
        e1 = [0] * n
        for c in cs[:2]:
            e1[c] = random.randrange(1, q)
        e0 = [0] * n
        e0[cs[0]] = (-g1 * e1[cs[0]]) % q
        e0[cs[1]] = (-g2 * e1[cs[1]]) % q
        # extra noise to open a third decode lane
        e0[cs[2]] = random.randrange(q)
        e1[cs[3]] = random.randrange(q)
        u0 = tuple((w0[i] + e0[i]) % q for i in range(n))
        u1 = tuple((w1[i] + e1[i]) % q for i in range(n))
        stacks.add((u0, u1))
    sC = run_point(q, n, k, domain, t, sorted(stacks), "C",
                   expect_window=False)
    print(f"[C GF(7) n=6 k=2 t=4 control outside window] {sC}")
    print(f"[C] control_breaks = {sC['control_breaks']} "
          f"(>0 confirms the window is load-bearing)")

    if bad_exit:
        print("PROBE FAILED")
        return 1
    print("PROBE OK: U1/W1/W2 hold in-window (non-vacuously); "
          f"outside-window breaks: {sC['control_breaks']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

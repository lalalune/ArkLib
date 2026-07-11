#!/usr/bin/env python3
"""probe_defeater_exactness.py — follow-ups to the S2(b) defeater (#357).

The rung sweep found a MissingLine DEFEATER at (F_3, n=4, k=1, l=2, |T|>=2):
a stack whose obstruction families need a hitting set of size 4 > q = 3 — at
delta = 1/2, which is EXACTLY the Johnson radius 1 - sqrt(1/4) of that code.

Two questions this probe decides:

(1) BELOW Johnson at the same code (|T| >= 3, delta = 1/4): does MissingLine hold?
    (Conjecture refinement: the obstruction bound is Johnson-gated.)

(2) Does the defeater break EXACTNESS itself? The obstruction bound is only a
    SUFFICIENT condition for `epsMCAG_interleaved_eq_of_obstructionBound`. Compute,
    for the identity generator (all seeds (a,b) in F^2) at delta = 1/2:
        - #bad seeds of the defeater interleaved stack U,
        - max over ALL base stacks f (2 single-column rows, up to codeword
          translation) of #bad seeds,
    and compare. If U's count exceeds the base max, interleaved generator-MCA error
    STRICTLY exceeds the base error — the first witnessed strict separation
    (the A(q,s) factor genuinely bites). If not, exactness survives the defeater
    and the obstruction bound is not necessary.

Exhaustive; exit 0 on completion.
"""

import itertools
import sys

P = 3
N = 4
DOMAIN = [0, 1, 2, 0]  # placeholder; fixed below


def main():
    # domain for n=4 over F_3: use all of F_3 plus... F_3 has only 3 elements, so a
    # 4-point "RS" domain does not exist over F_3 for distinct points. k=1 (constant
    # code) does not evaluate points at all, so the rung sweep's k=1/n=4 instance is
    # the REPETITION code on 4 abstract positions — keep that convention here.
    assert True
    NW = P ** N

    def w_decode(code):
        return tuple((code // P ** i) % P for i in range(N))

    def w_encode(w):
        return sum(a * P ** i for i, a in enumerate(w))

    # constant code on 4 positions
    cws = [tuple(c for _ in range(N)) for c in range(P)]
    cw_codes = sorted(w_encode(c) for c in cws)

    wadd = [[0] * NW for _ in range(NW)]
    wsmul = [[0] * NW for _ in range(P)]
    for x in range(NW):
        dx = w_decode(x)
        for c in range(P):
            wsmul[c][x] = w_encode(tuple((c * a) % P for a in dx))
        for y in range(NW):
            wadd[x][y] = w_encode(tuple((a + b) % P
                                        for a, b in zip(dx, w_decode(y))))

    def agree_sets(minT):
        ws = []
        for mask in range(1, 1 << N):
            members = [i for i in range(N) if mask >> i & 1]
            if len(members) >= minT:
                ws.append((mask, members))
        ab = []
        for mask, members in ws:
            bits = 0
            for code in range(NW):
                w = w_decode(code)
                if any(all((c // P ** i) % P == w[i] for i in members)
                       for c in cw_codes):
                    bits |= 1 << code
            ab.append(bits)
        return ws, ab

    seeds = list(itertools.product(range(P), repeat=2))

    # ---------- (1) below-Johnson rung: |T| >= 3 ----------
    ws3, ab3 = agree_sets(3)
    NM3 = len(ws3)
    lams = list(itertools.product(range(P), repeat=2))

    # coset reps (translation by constants)
    rep_seen = [False] * NW
    reps = []
    for x in range(NW):
        if rep_seen[x]:
            continue
        reps.append(x)
        for c in cw_codes:
            rep_seen[wadd[x][c]] = True

    lammask = {}
    for w0 in reps:
        for w1 in reps:
            lm = [0] * NM3
            for li, (l0, l1) in enumerate(lams):
                comb = wadd[wsmul[l0][w0]][wsmul[l1][w1]]
                for m in range(NM3):
                    if ab3[m] >> comb & 1:
                        lm[m] |= 1 << li
            lammask[(w0, w1)] = lm

    max_hit = 0
    argmax = None
    for r0 in itertools.product(reps, repeat=2):
        lm0 = lammask[r0]
        for r1 in itertools.product(reps, repeat=2):
            lm1 = lammask[r1]
            rows = (r0, r1)
            joint = []
            for m in range(NM3):
                a = ab3[m]
                joint.append(all(a >> r[0] & 1 and a >> r[1] & 1 for r in rows))
            fams = []
            distinct = set()
            for (sa, sb) in seeds:
                c0 = wadd[wsmul[sa][r0[0]]][wsmul[sb][r1[0]]]
                c1 = wadd[wsmul[sa][r0[1]]][wsmul[sb][r1[1]]]
                V = None
                for m in range(NM3):
                    if joint[m]:
                        continue
                    a = ab3[m]
                    if not (a >> c0 & 1 and a >> c1 & 1):
                        continue
                    K = lm0[m] & lm1[m]
                    if V is None:
                        V = set()
                    V.add(K)
                if V:
                    fams.append(V)
                    distinct |= V
            if not fams:
                continue
            uni = sorted(distinct)
            h = len(uni)
            for size in range(1, len(uni) + 1):
                if any(all(V & set(cb) for V in fams)
                       for cb in itertools.combinations(uni, size)):
                    h = size
                    break
            if h > max_hit:
                max_hit = h
                argmax = (rows, h, len(distinct))
    print(f"(1) below-Johnson rung (|T|>=3, delta=1/4): maxH={max_hit} "
          f"[H<=q: {'OK' if max_hit <= P else 'DEFEATER'}]  extremal={argmax}")

    # ---------- (2) exactness at the defeater (|T| >= 2, delta = 1/2) ----------
    ws2, ab2 = agree_sets(2)
    NM2 = len(ws2)

    def bad_count_interleaved(rows):
        joint = []
        for m in range(NM2):
            a = ab2[m]
            joint.append(all(a >> r[0] & 1 and a >> r[1] & 1 for r in rows))
        cnt = 0
        for (sa, sb) in seeds:
            c0 = wadd[wsmul[sa][rows[0][0]]][wsmul[sb][rows[1][0]]]
            c1 = wadd[wsmul[sa][rows[0][1]]][wsmul[sb][rows[1][1]]]
            for m in range(NM2):
                if joint[m]:
                    continue
                a = ab2[m]
                if a >> c0 & 1 and a >> c1 & 1:
                    cnt += 1
                    break
        return cnt

    def bad_count_base(f0, f1):
        # base stack: rows are single words
        joint = []
        for m in range(NM2):
            a = ab2[m]
            joint.append((a >> f0 & 1) and (a >> f1 & 1))
        cnt = 0
        for (sa, sb) in seeds:
            comb = wadd[wsmul[sa][f0]][wsmul[sb][f1]]
            for m in range(NM2):
                if joint[m]:
                    continue
                if ab2[m] >> comb & 1:
                    cnt += 1
                    break
        return cnt

    defeater = ((1, 3), (9, 13))
    bU = bad_count_interleaved(defeater)
    best_base = 0
    arg_base = None
    for f0 in reps:
        for f1 in range(NW):
            c = bad_count_base(f0, f1)
            if c > best_base:
                best_base = c
                arg_base = (f0, f1)
    # also: the max over ALL interleaved stacks of bad count, for context
    max_int = 0
    arg_int = None
    for r0 in itertools.product(reps, repeat=2):
        for r1 in itertools.product(reps, repeat=2):
            c = bad_count_interleaved((r0, r1))
            if c > max_int:
                max_int = c
                arg_int = (r0, r1)
    print(f"(2) exactness at delta=1/2 (identity generator, 9 seeds):")
    print(f"    defeater stack bad-seeds = {bU}")
    print(f"    max base-stack bad-seeds = {best_base}  (argmax {arg_base})")
    print(f"    max interleaved bad-seeds = {max_int}  (argmax {arg_int})")
    sep = "STRICT SEPARATION (factor bites!)" if max_int > best_base else \
        "exactness SURVIVES (obstruction bound not necessary)"
    print(f"    verdict: {sep}")
    print("exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())

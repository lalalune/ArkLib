#!/usr/bin/env python3
"""probe_missing_line_rungs.py — scaling rungs for the S2(b) hitting-number law (#357).

The F_3/n=3/l=2 exhaustive search (probe_missing_line_search.py) found the obstruction
hitting number H(U) bounded by the ROW COUNT l, not the field size q. This probe tests
the sharper law `H(U) <= l` (and the MissingLine bound `H(U) <= q`) on bigger rungs:

  * l = 3 rows at F_3 (does H track l?)            — the critical test
  * n = 4 at F_3 (does H grow with domain?)
  * F_5 (does H stay clear of q as q grows?)

Exhaustive **up to per-slot codeword translation**: every clause (line, joint, K_T) is
invariant under shifting any (row, column) word by a codeword, and the l*s slots shift
independently, so iterating over coset representatives covers all stacks exactly.

Seeds: all of F^l (identity generator — universal for any generator with l rows).
General s = 2 columns throughout (the MissingLine regime).

Output per rung: max H(U), max #distinct proper obstructions, the verdicts for
H <= l and H <= q. Exhaustive per rung: refutes or confirms at that scale.
"""

import itertools
import sys
import time


def run_rung(P, N, k, l, minT, label):
    t0 = time.time()
    DOMAIN = list(range(N))  # first N field points 0..N-1 (N <= P)
    NW = P ** N

    def w_decode(code):
        return tuple((code // P ** i) % P for i in range(N))

    def w_encode(w):
        return sum(a * P ** i for i, a in enumerate(w))

    # codewords of RS[F_P, domain, k]
    cws = set()
    for coeffs in itertools.product(range(P), repeat=k):
        cws.add(tuple(sum(c * pow(x, e, P) for e, c in enumerate(coeffs)) % P
                      for x in DOMAIN))
    cw_codes = sorted(w_encode(c) for c in cws)

    # word arithmetic
    wadd = [[0] * NW for _ in range(NW)]
    wsmul = [[0] * NW for _ in range(P)]
    for x in range(NW):
        dx = w_decode(x)
        for c in range(P):
            wsmul[c][x] = w_encode(tuple((c * a) % P for a in dx))
        for y in range(x, NW):
            dy = w_decode(y)
            s = w_encode(tuple((a + b) % P for a, b in zip(dx, dy)))
            wadd[x][y] = s
            wadd[y][x] = s

    # coset representatives (translation by codewords)
    rep = [0] * NW
    seen = [False] * NW
    reps = []
    for x in range(NW):
        if seen[x]:
            continue
        reps.append(x)
        for c in cw_codes:
            y = wadd[x][c]
            seen[y] = True
            rep[y] = x

    # witness masks
    wsets = []
    for mask in range(1, 1 << N):
        members = [i for i in range(N) if mask >> i & 1]
        if len(members) >= minT:
            wsets.append((mask, members))
    NM = len(wsets)

    agreebit = []
    for mask, members in wsets:
        bits = 0
        for code in range(NW):
            w = w_decode(code)
            if any(all((c // P ** i) % P == w[i] for i in members)
                   for c in cw_codes):
                bits |= 1 << code
        agreebit.append(bits)

    lams = list(itertools.product(range(P), repeat=2))
    seeds = list(itertools.product(range(P), repeat=l))

    # lammask[w0][w1][m]: bitmask over lams of explainable combinations (per row)
    lammask = {}
    for w0 in reps:
        for w1 in reps:
            lm = [0] * NM
            for li, (l0, l1) in enumerate(lams):
                comb = wadd[wsmul[l0][w0]][wsmul[l1][w1]]
                for m in range(NM):
                    if agreebit[m] >> comb & 1:
                        lm[m] |= 1 << li
            lammask[(w0, w1)] = lm

    max_hit = 0
    max_distinct = 0
    argmax = None
    n_stacks = 0
    # a stack = l rows, each row = (col0 word, col1 word), iterate over rep pairs
    row_choices = [(w0, w1) for w0 in reps for w1 in reps]
    for rows in itertools.product(row_choices, repeat=l):
        n_stacks += 1
        lms = [lammask[r] for r in rows]
        joint = []
        for m in range(NM):
            ab = agreebit[m]
            joint.append(all(ab >> r[0] & 1 and ab >> r[1] & 1 for r in rows))
        fams = []
        distinct = set()
        for seed in seeds:
            V = None
            # combined interleaved word per column
            c0 = 0
            c1 = 0
            for j in range(l):
                c0 = wadd[c0][wsmul[seed[j]][rows[j][0]]]
                c1 = wadd[c1][wsmul[seed[j]][rows[j][1]]]
            for m in range(NM):
                if joint[m]:
                    continue
                ab = agreebit[m]
                if not (ab >> c0 & 1 and ab >> c1 & 1):
                    continue
                K = (1 << len(lams)) - 1
                for j in range(l):
                    K &= lms[j][m]
                if V is None:
                    V = set()
                V.add(K)
            if V:
                fams.append(V)
                distinct |= V
        if not fams:
            continue
        nd = len(distinct)
        if nd > max_distinct:
            max_distinct = nd
        uni = sorted(distinct)
        h = len(uni)
        for size in range(1, len(uni) + 1):
            done = False
            for combo in itertools.combinations(uni, size):
                cs = set(combo)
                if all(V & cs for V in fams):
                    done = True
                    break
            if done:
                h = size
                break
        if h > max_hit:
            max_hit = h
            argmax = (rows, h, nd)
    dt = time.time() - t0
    okl = "OK" if max_hit <= l else "VIOLATED"
    okq = "OK" if max_hit <= P else "DEFEATER (S2(b) FALSE here)"
    print(f"{label}: stacks(up to translation)={n_stacks} maxH={max_hit} "
          f"maxDistinct={max_distinct}  [H<=l: {okl}] [H<=q: {okq}]  ({dt:.0f}s)")
    if argmax:
        print(f"    extremal rows={argmax[0]} H={argmax[1]} distinct={argmax[2]}")
    return max_hit


def main():
    print("S2(b) scaling rungs (s=2; seeds = all of F^l; exhaustive up to "
          "codeword translation)")
    results = {}
    results["F3 n3 k1 l3 T>=2"] = run_rung(3, 3, 1, 3, 2, "F3 n3 k1 l3 T>=2")
    results["F3 n4 k1 l2 T>=2"] = run_rung(3, 4, 1, 2, 2, "F3 n4 k1 l2 T>=2")
    results["F3 n4 k2 l2 T>=2"] = run_rung(3, 4, 2, 2, 2, "F3 n4 k2 l2 T>=2")
    results["F3 n4 k2 l2 T>=3"] = run_rung(3, 4, 2, 2, 3, "F3 n4 k2 l2 T>=3")
    results["F5 n3 k1 l2 T>=2"] = run_rung(5, 3, 1, 2, 2, "F5 n3 k1 l2 T>=2")
    results["F5 n3 k2 l2 T>=2"] = run_rung(5, 3, 2, 2, 2, "F5 n3 k2 l2 T>=2")
    print("\nsummary:", results)
    print("exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())

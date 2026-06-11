#!/usr/bin/env python3
"""probe_missing_line_search.py — exhaustive S2(b) MissingLine search (#357).

Hypothesis S2(b): at s = 2, no single stack U realizes an obstruction structure that
defeats a q-element dominating family — equivalently, in `Jo26ObstructionCount.lean`
terms, `MissingLine C delta G U` holds for every U.

A stack DEFEATS MissingLine iff for every family Ls of <= q proper subspaces of F^2,
some bad seed has ALL its witnesses' obstruction subspaces K_T outside Ls. We measure,
for every stack U (exhaustively: F_3, n = 3, l = 2 rows, s = 2 columns, k = 1 and 2):

  * per-bad-seed sets V_omega = { K_T : T a witness of omega } (K_T as the 9-bit mask
    of explainable combiners; properness is automatic from the witness's third clause),
  * the exact minimum hitting-set size H(U) over the realized obstruction values,
  * the number of distinct proper obstruction subspaces realized by U.

S2(b) at this scale  <=>  max_U H(U) <= q = 3.

Seeds: ALL coefficient pairs (a, b) in F^2 (identity generator) — universal for l = 2.
Radius: |T| >= 2 of n = 3 (delta = 1/3). Exhaustive; can only confirm or refute, not
under-report.

Encoding: column words (3 trits) as ints 0..26; per-witness-mask agreement sets as
27-bit masks; K_T = AND of two precomputed 9-bit lambda-masks.
"""

import itertools
import sys

P = 3
N = 3
DOMAIN = [0, 1, 2]
NW = P ** N  # 27 column words


def w_encode(w):
    return w[0] + P * w[1] + P * P * w[2]


def w_decode(code):
    return (code % P, (code // P) % P, (code // (P * P)) % P)


def codewords(k):
    cws = set()
    for coeffs in itertools.product(range(P), repeat=k):
        cws.add(tuple(sum(c * pow(x, e, P) for e, c in enumerate(coeffs)) % P
                      for x in DOMAIN))
    return cws


def main():
    print(f"S2(b) MissingLine exhaustive search: F_{P}, n={N}, l=2, s=2, |T|>=2")
    print(f"q = {P}; defeat <=> min hitting set > {P}")

    # word arithmetic tables
    wadd = [[w_encode(tuple((a + b) % P for a, b in zip(w_decode(x), w_decode(y))))
             for y in range(NW)] for x in range(NW)]
    wsmul = [[w_encode(tuple((c * a) % P for a in w_decode(x)))
              for x in range(NW)] for c in range(P)]

    # witness masks: subsets of {0,1,2} with >= 2 members
    wsets = []
    for mask in range(1, 1 << N):
        members = [i for i in range(N) if mask >> i & 1]
        if len(members) >= 2:
            wsets.append((mask, members))

    seeds = list(itertools.product(range(P), repeat=2))
    lams = list(itertools.product(range(P), repeat=2))
    NL = len(lams)  # 9

    for k in (1, 2):
        cws = codewords(k)
        # agree bit per (wmask index, word)
        agreebit = []
        for mask, members in wsets:
            bits = 0
            for code in range(NW):
                w = w_decode(code)
                if any(all(c[i] == w[i] for i in members) for c in cws):
                    bits |= 1 << code
            agreebit.append(bits)
        NM = len(wsets)

        # lammask[w0][w1][m] = 9-bit mask of lambdas with (lam0*w0+lam1*w1) agreeing on wsets[m]
        # colword[w0][w1][seedidx] = combined word under seed (a,b)
        lammask = [[[0] * NM for _ in range(NW)] for _ in range(NW)]
        colword = [[[0] * len(seeds) for _ in range(NW)] for _ in range(NW)]
        for w0 in range(NW):
            for w1 in range(NW):
                for li, (l0, l1) in enumerate(lams):
                    comb = wadd[wsmul[l0][w0]][wsmul[l1][w1]]
                    for m in range(NM):
                        if agreebit[m] >> comb & 1:
                            lammask[w0][w1][m] |= 1 << li
                for si, (a, b) in enumerate(seeds):
                    colword[w0][w1][si] = wadd[wsmul[a][w0]][wsmul[b][w1]]

        max_hit = 0
        max_distinct = 0
        argmax = None
        n_stacks = 0
        rng = range(NW)
        for r00 in rng:
            for r01 in rng:
                lm0 = lammask[r00][r01]
                for r10 in rng:
                    lm1row = lammask[r10]
                    cw0row = colword[r00]  # wait: columns pair rows, fix below
                    for r11 in rng:
                        n_stacks += 1
                        lm1 = lm1row[r11]
                        # joint clause per mask: all four base words explainable
                        # column words: col0 = (r00 from row0, r10 from row1)...
                        # base words are r00,r01 (row0 cols) and r10,r11 (row1 cols)
                        fams = []
                        distinct = set()
                        # per-mask joint check
                        joint = [
                            (agreebit[m] >> r00 & 1) and (agreebit[m] >> r01 & 1)
                            and (agreebit[m] >> r10 & 1) and (agreebit[m] >> r11 & 1)
                            for m in range(NM)
                        ]
                        for si in range(len(seeds)):
                            # combined interleaved word: column c word combines
                            # row0 col c and row1 col c under (a,b)
                            c0 = colword[r00][r10][si]
                            c1 = colword[r01][r11][si]
                            V = None
                            for m in range(NM):
                                if joint[m]:
                                    continue
                                ab = agreebit[m]
                                if not (ab >> c0 & 1 and ab >> c1 & 1):
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
                        nd = len(distinct)
                        if nd > max_distinct:
                            max_distinct = nd
                        # exact min hitting set (universe tiny)
                        uni = sorted(distinct)
                        h = None
                        for size in range(1, len(uni) + 1):
                            found = False
                            for combo in itertools.combinations(uni, size):
                                cs = set(combo)
                                if all(V & cs for V in fams):
                                    found = True
                                    break
                            if found:
                                h = size
                                break
                        if h is None:
                            h = len(uni)
                        if h > max_hit:
                            max_hit = h
                            argmax = ((r00, r01, r10, r11), h, nd)
        verdict = ("DEFEATER FOUND — S2(b) FALSE at this scale" if max_hit > P
                   else "no defeater — MissingLine HOLDS exhaustively")
        print(f"\nk={k}: stacks={n_stacks}  max min-hitting-set={max_hit}  "
              f"max distinct proper obstructions per stack={max_distinct}")
        print(f"  verdict: {verdict}")
        if argmax:
            print(f"  extremal stack (row-col words r00,r01,r10,r11): {argmax[0]}  "
                  f"hit={argmax[1]} distinct={argmax[2]}")
    print("\nexit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""probe_missing_line_l3.py — S2(b) discriminator: 3-row stacks (l = 3) (#357).

The F3/F5 two-row rungs all satisfy H(U) = min(l, r) where l = #rows and
r = n - k = the syndrome dimension — but every binding case there had l = r = 2,
so the data cannot tell the row law `H <= l` from the syndrome law `H <= r`.

This probe is one of the two discriminating experiments (the other is the heavy
l=2, r=3 rung): three-row stacks over F_3 and F_5 at n = 3, k = 1 (r = 2, s = 2).

  * row law      predicts max H <= 3
  * syndrome law predicts max H <= 2

A single stack with H = 3 kills the syndrome law; exhaustive H <= 2 is strong
evidence for it (and for `ObstructionBound` with a family far smaller than q).

Same exact symmetries as the l=2 probe (verified to preserve {V_omega} and H):
per-row codeword translation, per-row scaling, row permutation (S_3 here).
Seeds: ALL coefficient triples in F^3 — universal for l = 3 generators.
"""

import itertools
import sys
import time


def run_rung(P, domain, k, minT, label):
    N = len(domain)
    NW = P ** N
    t0 = time.time()
    print(f"\n=== {label}: F_{P}, n={N}, k={k}, |T|>={minT}, l=3, s=2 ===")
    print("row law: H <= 3; syndrome law: H <= r =", N - k)

    def w_encode(w):
        c = 0
        for i in reversed(range(N)):
            c = c * P + w[i]
        return c

    def w_decode(code):
        out = []
        for _ in range(N):
            out.append(code % P)
            code //= P
        return tuple(out)

    cws = set()
    for coeffs in itertools.product(range(P), repeat=k):
        cws.add(tuple(sum(c * pow(x, e, P) for e, c in enumerate(coeffs)) % P
                      for x in domain))
    cw_codes = sorted(w_encode(c) for c in cws)

    wadd = [[w_encode(tuple((a + b) % P for a, b in zip(w_decode(x), w_decode(y))))
             for y in range(NW)] for x in range(NW)]
    wsmul = [[w_encode(tuple((c * a) % P for a in w_decode(x)))
              for x in range(NW)] for c in range(P)]

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
            if any(all(c[i] == w[i] for i in members) for c in cws):
                bits |= 1 << code
        agreebit.append(bits)

    rep = [0] * NW
    for code in range(NW):
        rep[code] = min(wadd[code][c] for c in cw_codes)

    units = [a for a in range(1, P)]
    seen = set()
    rows = []
    for w0 in range(NW):
        if rep[w0] != w0:
            continue
        for w1 in range(NW):
            if rep[w1] != w1:
                continue
            cand = min((rep[wsmul[a][w0]], rep[wsmul[a][w1]]) for a in units)
            if cand in seen:
                continue
            seen.add(cand)
            rows.append(cand)
    rows.sort()
    NR = len(rows)
    n_stacks_total = NR * (NR + 1) * (NR + 2) // 6
    print(f"canonical rows: {NR}; 3-row stacks to scan: {n_stacks_total}")

    seeds = list(itertools.product(range(P), repeat=3))
    lams = list(itertools.product(range(P), repeat=2))

    LM = []
    RJ = []
    for (w0, w1) in rows:
        lmrow = []
        rj = 0
        for m in range(NM):
            ab = agreebit[m]
            bits = 0
            for li, (l0, l1) in enumerate(lams):
                if ab >> wadd[wsmul[l0][w0]][wsmul[l1][w1]] & 1:
                    bits |= 1 << li
            lmrow.append(bits)
            if (ab >> w0 & 1) and (ab >> w1 & 1):
                rj |= 1 << m
        LM.append(lmrow)
        RJ.append(rj)

    max_hit = 0
    max_distinct = 0
    argmax = None
    n_stacks = 0
    full = (1 << NM) - 1
    for i in range(NR):
        for j in range(i, NR):
            rj01 = RJ[i] & RJ[j]
            for kk in range(j, NR):
                n_stacks += 1
                joint = rj01 & RJ[kk]
                if joint == full:
                    continue
                lm = (LM[i], LM[j], LM[kk])
                wrows = (rows[i], rows[j], rows[kk])
                active = [m for m in range(NM) if not (joint >> m & 1)]
                fams = []
                distinct = set()
                for (a, b, c) in seeds:
                    # seed combines the three rows, per column
                    c0 = wadd[wadd[wsmul[a][wrows[0][0]]][wsmul[b][wrows[1][0]]]][
                        wsmul[c][wrows[2][0]]]
                    c1 = wadd[wadd[wsmul[a][wrows[0][1]]][wsmul[b][wrows[1][1]]]][
                        wsmul[c][wrows[2][1]]]
                    V = None
                    for m in active:
                        ab2 = agreebit[m]
                        if not (ab2 >> c0 & 1 and ab2 >> c1 & 1):
                            continue
                        if V is None:
                            V = set()
                        V.add(lm[0][m] & lm[1][m] & lm[2][m])
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
                    found = False
                    for combo in itertools.combinations(uni, size):
                        cs = set(combo)
                        if all(V & cs for V in fams):
                            found = True
                            break
                    if found:
                        h = size
                        break
                if h > max_hit:
                    max_hit = h
                    argmax = (wrows, h, nd)
    print(f"stacks={n_stacks}  max min-hitting-set={max_hit}  "
          f"max distinct={max_distinct}")
    r = N - k
    verdict = []
    verdict.append("MissingLine HOLDS" if max_hit <= P else "DEFEATER (H > q)")
    verdict.append(f"row law H<=3 {'HOLDS' if max_hit <= 3 else 'FAILS'}")
    verdict.append(f"syndrome law H<=r={r} {'HOLDS' if max_hit <= r else 'FAILS'}")
    print("verdict: " + " · ".join(verdict))
    if argmax:
        print(f"extremal stack rows: {argmax[0]}  hit={argmax[1]} "
              f"distinct={argmax[2]}")
    print(f"[{label} done in {time.time() - t0:.1f}s]")
    return max_hit


def main():
    results = {}
    results["F3 k=1 (r=2)"] = run_rung(3, [0, 1, 2], 1, 2, "L3-F3 k=1")
    results["F3 k=2 (r=1)"] = run_rung(3, [0, 1, 2], 2, 2, "L3-F3 k=2")
    results["F5 k=1 (r=2)"] = run_rung(5, [0, 1, 2], 1, 2, "L3-F5 k=1")
    results["F5 k=2 (r=1)"] = run_rung(5, [0, 1, 2], 2, 2, "L3-F5 k=2")
    print("\n=== summary (l=3, s=2) ===")
    for tag, h in results.items():
        print(f"{tag}: max H = {h}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""probe_missing_line_f5_rungs.py — S2(b) MissingLine: the F5 scaling rungs (#357).

Successor to probe_missing_line_search.py (F3, n=3, exhaustive: max H(U) = 2 = l at
k=1, H = 1 at k=2; sharper law conjectured there: H(U) <= l, the number of stack
rows). This probe runs the F5 rungs to test BOTH scaling axes of that law:

  * field axis   : q 3 -> 5 at n = 3, k in {1, 2}        (rungs A1, A2)
  * length axis  : n 3 -> 4 (the SMOOTH domain <2> = F5*, the domain of the exact
                   delta* pin MCADeltaStarExactPoint.lean), k in {2, 3}  (B1, B2)
  * heavy rung   : n = 4, k = 1, |T| >= 3 (--rung heavy; hours, run in background)

Exhaustive **up to exact symmetries** of the obstruction structure, each verified to
preserve the per-seed obstruction-value families {V_omega} (hence H(U)) exactly:

  1. per-row translation by interleaved codewords (each base word independently
     reduces to its coset representative mod C),
  2. per-row scaling by F* (lambda-masks invariant; seeds permuted within the
     universal all-pairs seed set),
  3. row swap (K_T is a row-intersection; seeds permuted).

A stack U DEFEATS MissingLine iff its exact minimum hitting set H(U) over the
per-bad-seed obstruction families exceeds q. The probe reports max H(U) and the
max number of distinct proper obstruction values per stack.

S2(b) at a rung      <=>  max_U H(U) <= q.
Sharper law (S2(b)+) <=>  max_U H(U) <= l = 2.

Seeds: ALL coefficient pairs (a, b) in F^2 — universal for l = 2 generators.
Properness of every collected K is automatic: K = top contains both unit vectors,
which makes every base word explainable on T, i.e. the mask would be joint.
"""

import argparse
import itertools
import sys
import time


def run_rung(P, domain, k, minT, label):
    N = len(domain)
    NW = P ** N
    t0 = time.time()
    print(f"\n=== {label}: F_{P}, n={N}, domain={domain}, k={k}, |T|>={minT}, "
          f"l=2, s=2 ===")
    print(f"q = {P}; defeat <=> min hitting set > {P}; sharper law <=> max H <= 2")

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

    # codewords: evaluations of degree-<k polynomials on `domain`
    cws = set()
    for coeffs in itertools.product(range(P), repeat=k):
        cws.add(tuple(sum(c * pow(x, e, P) for e, c in enumerate(coeffs)) % P
                      for x in domain))
    cw_codes = sorted(w_encode(c) for c in cws)

    # word arithmetic tables
    wadd = [[w_encode(tuple((a + b) % P for a, b in zip(w_decode(x), w_decode(y))))
             for y in range(NW)] for x in range(NW)]
    wsmul = [[w_encode(tuple((c * a) % P for a in w_decode(x)))
              for x in range(NW)] for c in range(P)]

    # witness masks with |T| >= minT
    wsets = []
    for mask in range(1, 1 << N):
        members = [i for i in range(N) if mask >> i & 1]
        if len(members) >= minT:
            wsets.append((mask, members))
    NM = len(wsets)

    # agreement bit per (mask index, word): explainable on T by some codeword
    agreebit = []
    for mask, members in wsets:
        bits = 0
        for code in range(NW):
            w = w_decode(code)
            if any(all(c[i] == w[i] for i in members) for c in cws):
                bits |= 1 << code
        agreebit.append(bits)

    # coset representative mod codeword translation
    rep = [0] * NW
    for code in range(NW):
        rep[code] = min(wadd[code][c] for c in cw_codes)

    # canonical rows: (w0, w1) up to per-word translation and common scaling
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
    print(f"canonical rows: {NR} (of {NW * NW} raw pairs); "
          f"stacks to scan: {NR * (NR + 1) // 2}")

    seeds = list(itertools.product(range(P), repeat=2))
    lams = list(itertools.product(range(P), repeat=2))

    # per canonical row: lambda-mask per witness mask, and row-joint mask bits
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
    n_active = 0
    for i in range(NR):
        w00, w01 = rows[i]
        lm0 = LM[i]
        rj0 = RJ[i]
        for j in range(i, NR):
            n_stacks += 1
            w10, w11 = rows[j]
            joint = rj0 & RJ[j]
            if joint == (1 << NM) - 1:
                continue  # every mask joint: no bad seed possible
            lm1 = LM[j]
            active = [m for m in range(NM) if not (joint >> m & 1)]
            fams = []
            distinct = set()
            for (a, b) in seeds:
                c0 = wadd[wsmul[a][w00]][wsmul[b][w10]]
                c1 = wadd[wsmul[a][w01]][wsmul[b][w11]]
                V = None
                for m in active:
                    ab = agreebit[m]
                    if not (ab >> c0 & 1 and ab >> c1 & 1):
                        continue
                    if V is None:
                        V = set()
                    V.add(lm0[m] & lm1[m])
                if V:
                    fams.append(V)
                    distinct |= V
            if not fams:
                continue
            n_active += 1
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
                argmax = ((rows[i], rows[j]), h, nd)
    verdict = ("DEFEATER FOUND — S2(b) FALSE at this rung" if max_hit > P
               else "no defeater — MissingLine HOLDS exhaustively")
    law = ("sharper law H <= l HOLDS" if max_hit <= 2
           else f"sharper law H <= l FAILS (max H = {max_hit})")
    print(f"stacks={n_stacks} (with bad seeds: {n_active})  "
          f"max min-hitting-set={max_hit}  max distinct={max_distinct}")
    print(f"verdict: {verdict}; {law}")
    if argmax:
        print(f"extremal stack (rows as canonical word pairs): {argmax[0]}  "
              f"hit={argmax[1]} distinct={argmax[2]}")
    print(f"[{label} done in {time.time() - t0:.1f}s]")
    return max_hit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rung", default="fast", choices=["fast", "heavy"],
                    help="fast: A1,A2,B1,B2; heavy: n=4,k=1,|T|>=3 (hours)")
    args = ap.parse_args()

    results = {}
    if args.rung == "fast":
        # field-axis rungs (compare to the F3 n=3 exhaustive search)
        results["A1"] = run_rung(5, [0, 1, 2], 1, 2, "A1 field-axis k=1")
        results["A2"] = run_rung(5, [0, 1, 2], 2, 2, "A2 field-axis k=2")
        # length-axis rungs on the SMOOTH domain <2> = F5* (the exact-pin code)
        results["B1"] = run_rung(5, [1, 2, 4, 3], 2, 2, "B1 smooth n=4 k=2")
        results["B2"] = run_rung(5, [1, 2, 4, 3], 3, 2, "B2 smooth n=4 k=3")
    else:
        results["H1"] = run_rung(5, [1, 2, 4, 3], 1, 3, "H1 heavy n=4 k=1 |T|>=3")

    print("\n=== summary ===")
    for tag, h in results.items():
        print(f"{tag}: max H = {h}  ({'<= l=2 OK' if h <= 2 else 'law broken'})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""probe_missing_line_heavy_fast.py — S2(b) decisive rungs: n=4, k=1 (r=3) (#357).

The l=3 probe killed the row law as the binding quantity (l=3, r=2 stacks still
have H = 2 = r). Two refinements remain on the table:

  * syndrome law : H <= r = n - k
  * level law    : H <= #active witness levels
                   (= # distinct dims of N_T = (C + Z_T)/C over allowed masks)

At every rung run so far the two coincide. The discriminators, both run here
(F_5, n=4, k=1, so r = 3, l = 2 rows, s = 2 columns):

  * minT=3 : levels = 2 (|T| in {3,4}), r = 3.  H=3 kills the level law.
  * minT=2 : levels = 3 (|T| in {2,3,4}), r = 3. H=3 kills `H <= min(l,r)` and
             the l-law conclusively; H<=2 with minT=2 would kill the pure r-law
             (since r=3) and crown the level law... except levels=3 here too, so
             H<=2 at minT=2 would sharpen BELOW both laws. H here separates
             everything.

Exhaustive up to the exact symmetries (per-row codeword translation, per-row
scaling, row swap), as in the sibling probes. Performance: per-(coset-rep pair,
mask) seed bitmasks precomputed, and the hitting-set computation is memoized on
the (K-values, seed-bitmask) configuration — the stack loop is pure table ops.

Seeds: all 25 coefficient pairs (universal for l=2).
"""

import argparse
import itertools
import sys
import time


def run_rung(P, domain, k, minT, label):
    N = len(domain)
    NW = P ** N
    t0 = time.time()
    print(f"\n=== {label}: F_{P}, n={N}, k={k}, |T|>={minT}, l=2, s=2 ===", flush=True)

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
    reps = sorted(set(rep))
    ridx = {w: i for i, w in enumerate(reps)}
    NRW = len(reps)

    units = [a for a in range(1, P)]
    seen = set()
    rows = []
    for w0 in reps:
        for w1 in reps:
            cand = min((rep[wsmul[a][w0]], rep[wsmul[a][w1]]) for a in units)
            if cand in seen:
                continue
            seen.add(cand)
            rows.append(cand)
    rows.sort()
    NR = len(rows)
    print(f"coset reps: {NRW}; canonical rows: {NR}; "
          f"stacks: {NR * (NR + 1) // 2}", flush=True)

    seeds = list(itertools.product(range(P), repeat=2))
    NS = len(seeds)
    lams = seeds

    # per canonical row: lambda-mask per witness mask + row-joint bits
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
        LM.append(tuple(lmrow))
        RJ.append(rj)

    # SEEDMASK[i1][i2][m]: bitmask over seeds whose row-combination of
    # (reps[i1], reps[i2]) is m-explainable
    SEEDMASK = [[None] * NRW for _ in range(NRW)]
    for i1, x in enumerate(reps):
        for i2, y in enumerate(reps):
            cell = []
            for m in range(NM):
                ab = agreebit[m]
                bits = 0
                for si, (a, b) in enumerate(seeds):
                    if ab >> wadd[wsmul[a][x]][wsmul[b][y]] & 1:
                        bits |= 1 << si
                cell.append(bits)
            SEEDMASK[i1][i2] = tuple(cell)
    print(f"[precompute done at {time.time() - t0:.1f}s]", flush=True)

    hit_cache = {}

    def hitting(Ks, sbs):
        # families: per seed, set of K values over active masks containing it
        fams = {}
        for mi in range(len(Ks)):
            sb = sbs[mi]
            K = Ks[mi]
            while sb:
                low = sb & -sb
                si = low.bit_length() - 1
                fams.setdefault(si, set()).add(K)
                sb ^= low
        if not fams:
            return 0, 0
        famlist = list(fams.values())
        distinct = set().union(*famlist)
        uni = sorted(distinct)
        for size in range(1, len(uni) + 1):
            for combo in itertools.combinations(uni, size):
                cs = set(combo)
                if all(V & cs for V in famlist):
                    return size, len(distinct)
        return len(uni), len(distinct)

    max_hit = 0
    max_distinct = 0
    argmax = None
    n_stacks = 0
    full = (1 << NM) - 1
    for i in range(NR):
        w00, w01 = rows[i]
        i00, i01 = ridx[w00], ridx[w01]
        lm0 = LM[i]
        rj0 = RJ[i]
        SM00 = SEEDMASK[i00]
        SM01 = SEEDMASK[i01]
        for j in range(i, NR):
            n_stacks += 1
            joint = rj0 & RJ[j]
            if joint == full:
                continue
            w10, w11 = rows[j]
            i10, i11 = ridx[w10], ridx[w11]
            lm1 = LM[j]
            sm0 = SM00[i10]
            sm1 = SM01[i11]
            Ks = []
            sbs = []
            for m in range(NM):
                if joint >> m & 1:
                    continue
                sb = sm0[m] & sm1[m]
                if not sb:
                    continue
                Ks.append(lm0[m] & lm1[m])
                sbs.append(sb)
            if not Ks:
                continue
            key = (tuple(Ks), tuple(sbs))
            res = hit_cache.get(key)
            if res is None:
                res = hitting(Ks, sbs)
                hit_cache[key] = res
            h, nd = res
            if nd > max_distinct:
                max_distinct = nd
            if h > max_hit:
                max_hit = h
                argmax = ((rows[i], rows[j]), h, nd)
                print(f"  new max H = {h} at rows {argmax[0]} "
                      f"(distinct={nd})", flush=True)
    r = N - k
    levels = len({N - len(mem) for _, mem in wsets} & set(range(0, r))) \
        if wsets else 0
    # active levels = distinct dims of N_T = n - |T| (capped at r), for |T| > k
    lvl = sorted({min(N - len(mem), r) for _, mem in wsets if len(mem) > k})
    print(f"stacks={n_stacks}  max min-hitting-set={max_hit}  "
          f"max distinct={max_distinct}  (cache size {len(hit_cache)})")
    print(f"r={r}, l=2, active levels={lvl} (count {len(lvl)})")
    verdict = []
    verdict.append("MissingLine HOLDS" if max_hit <= P else "DEFEATER (H > q)")
    verdict.append(f"l-law H<=2 {'HOLDS' if max_hit <= 2 else 'FAILS'}")
    verdict.append(f"r-law H<={r} {'HOLDS' if max_hit <= r else 'FAILS'}")
    verdict.append(f"level-law H<={len(lvl)} "
                   f"{'HOLDS' if max_hit <= len(lvl) else 'FAILS'}")
    print("verdict: " + " · ".join(verdict))
    if argmax:
        print(f"extremal stack rows: {argmax[0]}  hit={argmax[1]} "
              f"distinct={argmax[2]}")
    print(f"[{label} done in {time.time() - t0:.1f}s]", flush=True)
    return max_hit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--minT", type=int, default=3)
    ap.add_argument("--P", type=int, default=5)
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--k", type=int, default=1)
    args = ap.parse_args()
    if args.P == 5 and args.n == 4 and args.k >= 2:
        domain = [1, 2, 4, 3]
    else:
        # k=1 codes are the constants; the domain values are irrelevant
        domain = list(range(args.n))
    h = run_rung(args.P, domain, args.k, args.minT,
                 f"F{args.P} n={args.n} k={args.k} |T|>={args.minT}")
    print(f"\nmax H = {h}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

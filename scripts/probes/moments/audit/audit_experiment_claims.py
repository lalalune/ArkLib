#!/usr/bin/env python3
"""ADVERSARIAL AUDIT of O133 experiment-level claims from the LANDED JSONs.

(1) Re-derive separation ratios: cloud diameter (max pairwise max-abs M3 diff
    among random domains) vs min distance subgroup->cloud, at q=113 and q=257
    n=16; check 14.1x / 10.8x and same-sign argmax (2,2,2) claims.
(2) Re-run my own census on the LANDED subgroup domains at q=113/257 and check:
    - t2 histogram == landed census,
    - spike set {t2 >= 7} == {(1,0,(q-c)%q): c in H} | {(0,1,0)} EXACTLY,
    - spectral gap: no pencil with t2 in {4,5,6},
    - t2 values of the spike family in {(n-2)/2, n/2} with the QR split.
(3) AP census at n=16 (not produced by the landed experiment): do additive
    pencils (0,1,c) spike?
"""
import json
import sys
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent


def load(tag):
    return json.load(open(HERE / "experiment" / f"{tag}.json"))


def tdiff(a, b):
    keys = set(a["M3"]) | set(b["M3"])
    worst, arg = 0, None
    sub_bigger_222 = None
    for kk in keys:
        va, vb = int(a["M3"].get(kk, 0)), int(b["M3"].get(kk, 0))
        d = abs(va - vb)
        if d > worst:
            worst, arg = d, kk
    return worst, arg


def census(q, D):
    n = len(D)
    pairs = list(combinations(D, 2))
    phis = [(1, b, c) for b in range(q) for c in range(q)] + \
           [(0, 1, c) for c in range(q)] + [(0, 0, 1)]
    hist, high = {}, []
    for (f0, f1, f2) in phis:
        uni = {x for x in D if f0 == 1 and f1 == x and f2 == (x * x) % q}
        t2 = 0
        touched = {}
        for (x, y) in pairs:
            if x in uni or y in uni:
                continue
            if (f0 * x * y - f1 * (x + y) + f2) % q == 0:
                t2 += 1
                touched[x] = touched.get(x, 0) + 1
                touched[y] = touched.get(y, 0) + 1
        assert all(v == 1 for v in touched.values()), (f0, f1, f2)
        hist[t2] = hist.get(t2, 0) + 1
        if t2 >= 4:
            high.append(((f0, f1, f2), t2))
    assert sum(hist.values()) == q * q + q + 1
    assert sum(t * c for t, c in hist.items()) == (n * (n - 1) // 2) * (q - 1)
    return hist, high


def main():
    for q, rk in ((113, 14.1), (257, 10.8)):
        sub = load(f"k3_q{q}_n16_sub")
        rnd = [load(f"k3_q{q}_n16_rand{s}") for s in (1, 2, 3)]
        diam = 0
        for i in range(3):
            for j in range(i + 1, 3):
                w, _ = tdiff(rnd[i], rnd[j])
                diam = max(diam, w)
        dists = []
        for r in rnd:
            w, arg = tdiff(sub, r)
            v_sub = int(sub["M3"]["2,2,2"]); v_r = int(r["M3"]["2,2,2"])
            dists.append((w, arg, v_sub > v_r))
        sep = min(w for w, _, _ in dists)
        print(f"q={q}: cloud diameter = {diam:.3e}, min subgroup dist = {sep:.3e}, "
              f"ratio = {sep/diam:.2f} (claimed {rk})")
        print(f"   argmax keys: {[a for _, a, _ in dists]}, "
              f"sub M3[2,2,2] larger than each random: {[s for _, _, s in dists]}")

        H = sub["domain"]
        n = len(H)
        hist, high = census(q, H)
        landed_hist = {int(t): c for t, c in sub["census"]["t2_hist"].items()}
        print(f"   my census hist == landed: {hist == landed_hist}   hist={hist}")
        gap_empty = all(hist.get(t, 0) == 0 for t in (4, 5, 6))
        print(f"   spectral gap t2 in {{4,5,6}} empty: {gap_empty}")
        spikes = {phi for phi, t2 in high if t2 >= 7}
        pred = {(1, 0, (q - c) % q) for c in H} | {(0, 1, 0)}
        print(f"   spike set == normalizer family: {spikes == pred} "
              f"(|spikes|={len(spikes)}, |pred|={len(pred)})")
        t2map = dict(high)
        vals = sorted({t2 for phi, t2 in high if t2 >= 7})
        print(f"   spike t2 values: {vals} (claim: {{(n-2)//2, n//2}} = {{7, 8}})")
        # QR split: t2 = 7 iff c = -f2 in H^2 (squares of H)
        H2 = {(x * x) % q for x in H}
        ok = all((t2map[(1, 0, (q - c) % q)] == (7 if c in H2 else 8)) for c in H)
        print(f"   QR split exact (c in H^2 <-> t2=7): {ok}")

        ap = load(f"k3_q{q}_n16_ap")
        hist_ap, high_ap = census(q, ap["domain"])
        add_spikes = [(phi, t2) for phi, t2 in high_ap if phi[0] == 0 and phi[1] == 1]
        print(f"   AP domain {ap['domain'][:4]}...: hist={hist_ap}")
        print(f"   AP additive-family entries with t2>=4: {add_spikes}")
        print(f"   AP top pencils: {sorted(high_ap, key=lambda r: -r[1])[:6]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

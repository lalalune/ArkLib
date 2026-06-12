#!/usr/bin/env python3
"""The separation experiment: does M3 distinguish smooth domains from random ones?

Issue #334 moments lane, probe protocol step 3 (HYPOTHESES-M3.md: H1, H2, A4, A5).
Engine: probe_agreement_m3_decomp.py (cross-validated exactly against the brute-force
ground truth before this experiment is believed). Everything exact integers.

Matrix (k=3): for each (q, n), compare the M3 tensor of
  subgroup        the order-n multiplicative subgroup H of F_q*
  coset           g*H for the smallest g not in H
  random_1..5     seeded uniform n-subsets of F_q* (random.Random(seed))
  ap              an arithmetic progression avoiding 0
  gpset           {g^e} for non-subgroup exponent sets (multiplicative structure,
                  not a subgroup; q=41 n=8 only)
against the subgroup's tensor and against each other (random-vs-random = null).

k=2 control (H2): subgroup vs randoms at q=41, n=8 — tensors must be EXACTLY equal.

Census (A4/A5): for the subgroup and one random domain, the pencil t2-histogram and
the spike list; checks the A5 prediction that subgroup spikes are EXACTLY
  {phi = (1,0,f2) : -f2 in c-set} (the involutions x -> c/x stabilizing the domain)
  + {phi = (0,1,0)} (x -> -x, present since -1 in H for even n),
with c-set = H for the subgroup and g^2 H for the coset gH.

Output: RESULTS-M3-RAW.md (tables) + per-run JSONs under experiment/.
"""

import json
import random
import subprocess
import sys
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
ENGINE = HERE / "probe_agreement_m3_decomp.py"
OUTDIR = HERE / "experiment"
OUTDIR.mkdir(exist_ok=True)


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q):
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e)
        e = (e * h) % q
    return sorted(out)


def run_engine(q, k, domain, tag, census=False):
    path = OUTDIR / f"{tag}.json"
    cmd = ["taskset", "-c", "0-5", "nice", "-n", "10", "python3", str(ENGINE),
           "--q", str(q), "--k", str(k), "--domain", ",".join(map(str, domain)),
           "--json-out", str(path)]
    if census:
        cmd.append("--census")
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"ENGINE FAILED for {tag}:\n{r.stderr[-2000:]}")
        sys.exit(1)
    return json.loads(r.stdout)


def tensor_diff(a, b):
    """(#differing keys, max abs diff, argmax key, value pair at argmax)"""
    keys = set(a["M3"]) | set(b["M3"])
    worst, arg, pair, ndiff = 0, None, None, 0
    for kk in keys:
        va, vb = a["M3"].get(kk, 0), b["M3"].get(kk, 0)
        d = abs(va - vb)
        if d:
            ndiff += 1
            if d > worst:
                worst, arg, pair = d, kk, (va, vb)
    return ndiff, worst, arg, pair


def main():
    lines = ["# RESULTS-M3-RAW — the separation experiment (exact, engine cross-validated)",
             "", "Null hypothesis H0: M3 is domain-independent at fixed (q,n,k).",
             "Engine asserts hold on every run (incl. sum_phi t2 == C(n,2)(q-1) for ALL domains).", ""]

    # ---------------- k=2 control (H2) ----------------
    q, n = 41, 8
    sub = run_engine(q, 2, subgroup(q, n), f"k2_q{q}_sub")
    ctrl_equal = True
    for seed in (1, 2):
        dom = sorted(random.Random(seed).sample(range(1, q), n))
        r = run_engine(q, 2, dom, f"k2_q{q}_rand{seed}")
        nd, w, arg, pair = tensor_diff(sub, r)
        ctrl_equal &= (nd == 0)
        lines.append(f"k=2 control q={q} n={n} subgroup vs random_{seed}: "
                     f"{'EXACTLY EQUAL' if nd == 0 else f'DIFFER ({nd} keys, max {w} at {arg})'}")
    lines.append(f"\n**H2 verdict: k=2 M3 domain-independent = {ctrl_equal}**\n")

    # ---------------- k=3 matrix ----------------
    matrix = [
        (41, 8, dict(coset=True, nrandom=5, ap=[3, 7, 11, 15, 19, 23, 27, 31], gpset=True)),
        (41, 10, dict(coset=False, nrandom=3, ap=[1 + 4 * i for i in range(10)], gpset=False)),
        (113, 16, dict(coset=False, nrandom=3, ap=[2 + 7 * i for i in range(16)], gpset=False)),
        (257, 16, dict(coset=False, nrandom=3, ap=[3 + 16 * i for i in range(16)], gpset=False)),
    ]
    k3_separation = False
    for (q, n, cfg) in matrix:
        H = subgroup(q, n)
        runs = {"subgroup": run_engine(q, 3, H, f"k3_q{q}_n{n}_sub", census=True)}
        if cfg["coset"]:
            Hset = set(H)
            g = next(x for x in range(2, q) if x not in Hset)
            runs["coset"] = run_engine(q, 3, sorted(x * g % q for x in H), f"k3_q{q}_n{n}_coset")
        for seed in range(1, cfg["nrandom"] + 1):
            dom = sorted(random.Random(seed).sample(range(1, q), n))
            runs[f"random_{seed}"] = run_engine(q, 3, dom, f"k3_q{q}_n{n}_rand{seed}",
                                                census=(seed == 1))
        assert all(a % q != 0 for a in cfg["ap"]), "AP touches 0"
        runs["ap"] = run_engine(q, 3, sorted(cfg["ap"]), f"k3_q{q}_n{n}_ap")
        if cfg["gpset"]:
            g = primitive_root(q)
            dom = sorted({pow(g, e, q) for e in (1, 2, 4, 8, 16, 32, 25, 11)})
            assert len(dom) == n
            runs["gpset"] = run_engine(q, 3, dom, f"k3_q{q}_n{n}_gpset")

        lines.append(f"## k=3, q={q}, n={n}")
        lines.append("| domain | #keys differing vs subgroup | max abs diff | at (j1,j2,j3) | (sub, dom) there |")
        lines.append("|---|---|---|---|---|")
        base = runs["subgroup"]
        for name, r in runs.items():
            if name == "subgroup":
                continue
            nd, w, arg, pair = tensor_diff(base, r)
            if nd and not name.startswith("random_vs"):
                k3_separation = True
            lines.append(f"| {name} | {nd} | {w} | {arg} | {pair} |")
        # null baseline: random_1 vs random_2
        if cfg["nrandom"] >= 2:
            nd, w, arg, pair = tensor_diff(runs["random_1"], runs["random_2"])
            lines.append(f"| random_1 vs random_2 (null) | {nd} | {w} | {arg} | {pair} |")
        lines.append("")

        # census: subgroup spikes + A5 check
        cen = base.get("census", {})
        lines.append(f"subgroup t2 histogram: {cen.get('t2_hist')}")
        spikes = cen.get("high_t2", [])
        lines.append(f"subgroup spikes (t2 >= 3): {len(spikes)}")
        Hset = set(H)
        pred = {(1, 0, (q - c) % q) for c in Hset}  # phi=(1,0,f2), -f2 in H
        pred.add((0, 1, 0))
        got = {tuple(s["phi"]) for s in spikes}
        # A5 is about the LARGE spikes; report set relations exactly
        big = {tuple(s["phi"]) for s in spikes if s["t2"] >= max(3, n // 2 - 1)}
        lines.append(f"A5 predicted family ({len(pred)} pencils): "
                     f"big-spike set == predicted: {big == pred}; "
                     f"extra big spikes ({len(big - pred)}): {sorted(big - pred)}; "
                     f"missed predictions ({len(pred - big)}): {sorted(pred - big)}")
        if "census" in runs.get("random_1", {}):
            lines.append(f"random_1 t2 histogram: {runs['random_1']['census'].get('t2_hist')}")
        lines.append("")

    lines.append(f"**H1 verdict: k=3 separation observed = {k3_separation}**")
    out = HERE / "RESULTS-M3-RAW.md"
    out.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())

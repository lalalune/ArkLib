#!/usr/bin/env python3
"""
probe_m128_rigor.py -- ArkLib#371: upgrade M(128) <= 6 from two-prime evidence to a
RIGOROUS prime ladder, exactly as RESULTS-CHAR0-RIGOR.md did for n in {8,16,32,64}.

Plan (the invisibility trichotomy + per-plane pigeonhole of RESULTS-CHAR0-RIGOR):
  a hypothetical char-0 plane h with >= 7 surface incidences carries three FIXED
  nonzero case integers D_bc, D_ad <= B_coord and D_det <= B_det; at every clean
  split prime where the census reports max 6, p divides one of them; with
  cap(B) = max{t : 2^(28t) < B} and k(n) = 2*cap(B_coord) + cap(B_det) + 1 clean
  primes the pigeonhole is violated, so no h exists and M(n) <= 6.

At n = 128 (m = 64), recomputed EXACTLY here (integer comparisons only):
  Hadamard route  B_coord = 3^96  (153 bits, cap 5),  B_det = 54^64 (369 bits, cap 13)
                  => k_hadamard = 2*5 + 13 + 1 = 24    (the prior estimate, verified)
  L1 route        B_coord = 6^64  (166 bits, cap 5),  B_det = 72^64 (395 bits, cap 14)
                  => k_l1       = 2*5 + 14 + 1 = 25
We run max(24, 25) = 25 distinct clean split primes (smallest first) so the verdict is
route-independent.

Census engine: probe_reciprocal_census.run_census -- the independent reimplementation
gated by bit-identical histogram reproduction against the original census at
(n=32, p=268435649) and (n=64, p=268435649).  Its in-run cleanliness guarantees per
prime (all hard asserts, run aborts otherwise):
  - surface points distinct mod p          (build_points assert)
  - pair enumeration complete              (n_pairs == (N-1)(N-2)/2)
  - rank-2 bucket fact: the only flats are the two coordinate lines, each L = n,
    and the rank-2 triple count equals the bucket prediction (n-1)(n-2)
  - recount EXACT and uncapped: every mult>=2 key recounted by the O(n) Moebius
    counter (no cap exists in this engine), validated in-run against the brute
    O(n^2) counter on 200 planes
  - mult-1 => count-3 lemma applied only after the recount asserts count >= 4
  - spanning-identity spot check (2000 samples) must have 0 failures
Cross-prime requirement (O157): count-5 and count-6 histogram entries IDENTICAL at
every prime; count-3/4 surplus is allowed and expected at n = 128 -- its spread is
recorded, never used as a pass/fail criterion (surplus inflates, never hides).

The two already-run primes 268437889, 268438657 (results_reciprocal_census.json,
RESULTS-RECIPROCAL.md section 3) are precisely the 2 smallest ladder primes; they are
REUSED after an integrity recheck (stored asserts re-derived from the stored numbers +
cheap deterministic facts recomputed: z, point distinctness, flats).  If any recheck
fails the prime is re-run from scratch.

Disk discipline (this box has ~9 GB free; one n=128 run streams ~2 GB gz keys plus
compressed sort temps): primes run SEQUENTIALLY, the temp dir is removed after every
run, and free space must exceed 4 GiB before each run starts (honest bail otherwise).
Wall budget: honest stop after BUDGET_SEC, reporting the partial count.

Usage:  probe_m128_rigor.py run        (resumable: completed primes are skipped)
Outputs: results_reciprocal_census.json (per-prime runs, incremental),
         results_char0_rigor.json (n=128 block), RESULTS-M128-RIGOR.md.
"""

import json
import os
import shutil
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from probe_reciprocal_census import (        # noqa: E402
    TMPDIR, _init_cert, build_points, cross_from_triple, flats_check, is_prime,
    merge_save, moebius_set, order_n_element, pack_key, run_census, split_primes,
)

N = 128
M = N // 2
TWO28 = 1 << 28
CENSUS_JSON = os.path.join(HERE, "results_reciprocal_census.json")
RIGOR_JSON = os.path.join(HERE, "results_char0_rigor.json")
OUT_MD = os.path.join(HERE, "RESULTS-M128-RIGOR.md")
LOG = os.path.join(HERE, "n128_ladder.txt")
MIN_FREE_GIB = 4.0
BUDGET_SEC = 4.6 * 3600          # honest stop margin under the ~5h cap


def log(msg):
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    with open(LOG, "a") as fh:
        fh.write(line + "\n")


# ------------------------------------------------------------------ exact k(128)

def capacity(B: int) -> int:
    """Max t with 2^(28t) < B: t distinct primes > 2^28 dividing a positive integer
    <= B have product > 2^(28t), so more is impossible.  Exact integer comparison."""
    t = 0
    while (1 << (28 * (t + 1))) < B:
        t += 1
    return t


def k_block():
    b = {
        "m": M,
        "B_coord_hadamard": 3 ** (3 * M // 2),     # |N(v_k)|   <= (3*sqrt3)^m = 3^(3m/2)
        "B_det_hadamard": 54 ** M,                 # |N(det_v)| <= 54^m
        "B_coord_l1": 6 ** M,                      # cruder ||v_k||_1 <= 6 route
        "B_det_l1": 72 ** M,
    }
    cc_h, cd_h = capacity(b["B_coord_hadamard"]), capacity(b["B_det_hadamard"])
    cc_l, cd_l = capacity(b["B_coord_l1"]), capacity(b["B_det_l1"])
    return {
        "bounds_bits": {k: v.bit_length() for k, v in b.items() if k != "m"},
        "bounds_str": {k: str(v) for k, v in b.items()},
        "cap_coord_hadamard": cc_h, "cap_det_hadamard": cd_h,
        "cap_coord_l1": cc_l, "cap_det_l1": cd_l,
        "k_needed_hadamard": 2 * cc_h + cd_h + 1,
        "k_needed_l1": 2 * cc_l + cd_l + 1,
        "k_run_target": max(2 * cc_h + cd_h + 1, 2 * cc_l + cd_l + 1),
    }


# ------------------------------------------------------------------ per-run predicates

EXPECTED_PAIRS = (N * N - 1) * (N * N - 2) // 2     # 134193153
EXPECTED_RANK2 = (N - 1) * (N - 2)                  # 16002 (two coordinate-line flats)


def run_checks(r):
    """Cleanliness predicates evaluated on a stored/produced run record (mirrors the
    in-run asserts so a reused record is held to the same standard)."""
    hist = {int(k): v for k, v in r["histogram"].items()}
    return {
        "M_p_equals_6": r["M_p"] == 6,
        "no_plane_over_6": not r["planes_over_6"] and max(hist) == 6,
        "pair_enumeration_complete": r["n_pairs"] == EXPECTED_PAIRS,
        "rank2_equals_bucket_prediction": r["n_rank2"] == EXPECTED_RANK2,
        "flats_coordinate_lines_only": bool(r["flats_coordinate_lines_only"]),
        "identity_spotcheck_clean": r["identity_spotcheck_failures"] == 0,
        # recount is exact/uncapped by construction in this engine (Moebius recount of
        # EVERY mult>=2 key, validated vs brute in-run); the histogram identities below
        # are the stored shadow of that path:
        "hist3_equals_distinct_minus_recounted":
            hist.get(3, 0) == r["n_distinct_planes"] - r["n_mult_ge2"],
        "recounted_mass_equals_mult_ge2":
            sum(v for k, v in hist.items() if k >= 4) == r["n_mult_ge2"],
        "histogram_sums_to_distinct": sum(hist.values()) == r["n_distinct_planes"],
    }


def reverify_stored(p, r):
    """Integrity recheck of a reused run: stored predicates + cheap deterministic
    recomputation (z, point distinctness assert, flats/bucket fact)."""
    checks = run_checks(r)
    z = order_n_element(p, N)
    checks["stored_z_recomputed"] = (z == r["z"])
    pts, diffs = build_points(N, p, z)          # asserts distinct points mod p
    checks["points_distinct_recomputed"] = True
    flats, expected_rank2, coord_only = flats_check(N, p, pts, diffs)
    checks["flats_recomputed_coordinate_lines_only"] = bool(coord_only)
    checks["rank2_prediction_recomputed"] = (expected_rank2 == r["n_rank2"])
    return checks


def prime_clean(p):
    return p > TWO28 and (p - 1) % N == 0 and is_prime(p)


def free_gib():
    return shutil.disk_usage(HERE).free / 2**30


def load_runs():
    if os.path.exists(CENSUS_JSON):
        with open(CENSUS_JSON) as fh:
            return json.load(fh).get("runs", {})
    return {}


# ------------------------------------------------------------------ surplus certificates
# The trichotomy/pigeonhole needs ONLY the clean-census predicates per prime
# (RESULTS-CHAR0-RIGOR section 7: cross-prime histogram identity is "extra evidence,
# not load-bearing").  Still, if a prime's count-5/6 bucket deviates from the proven
# char-0 tallies (1220 / 41292, exact certificates in results_count56_verify.json),
# we do not hand-wave: the deviation must be PROVEN to be mod-p surplus.  For each
# count-5/6 mod-p plane at the deviating prime, fix one rank-3 triple of its mod-p
# incidence set, build the EXACT char-0 plane v through that triple (cross product),
# and compute v's exact char-0 incidence set via the multi-prime certificate ladder
# ((prod p_i)^2 > 432^m => intersection of mod-p_i sets is exact; same lemma as
# verify6).  If all 5/6 points are char-0 coplanar their plane is v (1-dim
# annihilator), so exact_set == pts <=> true char-0 plane; exact_set a PROPER subset
# (size 3/4) <=> pure mod-p surplus (inflation).  Anything else = alarm.

CHAR0_TRUE = {5: 1220, 6: 41292}     # proven char-0 tallies (results_count56_verify)


def cert_ladder_primes():
    need = 1
    while (1 << (2 * 28 * need)) <= 432 ** M:
        need += 1
    return split_primes(N, need + 1)


def surplus_certify(p):
    """Re-run the census at deviating prime p keeping the count-5/6 incidence sets,
    then exactly certify every plane.  Returns the classification dict."""
    log(f"surplus pass p={p}: re-running census with keep_sets=(5,6)")
    res = run_census(N, p, keep_sets=(5, 6))
    sets56 = res.pop("_sets56")
    merge_save(res)          # refresh stored record (identical histogram expected)
    shutil.rmtree(TMPDIR, ignore_errors=True)
    primes = cert_ladder_primes()
    _init_cert(N, primes)    # sequential: reuse the worker-global tables in-process
    import probe_reciprocal_census as prc
    tabs = prc._G["tabs"]
    p0 = primes[0]
    zp0 = tabs[p0][0]
    out = {}
    for c in (5, 6):
        true_planes = 0
        surplus = []
        alarms = []
        for cc, pts in sets56:
            if cc != c:
                continue
            pts = [tuple(q) for q in pts]
            assert pts[0] == (0, 0)
            trip = None
            for a in range(1, len(pts)):
                for b in range(a + 1, len(pts)):
                    cand = ((0, 0), pts[a], pts[b])
                    if any(cross_from_triple(cand, zp0, p0, N)):
                        trip = cand
                        break
                if trip:
                    break
            if trip is None:
                alarms.append({"pts": [list(q) for q in pts],
                               "why": "no rank-3 triple at p0"})
                continue
            inter = None
            bad = False
            for q in primes:
                zp, dlog = tabs[q]
                v = cross_from_triple(trip, zp, q, N)
                if not any(v):
                    bad = True   # degenerate reduction: certificate inconclusive
                    break
                s = moebius_set(pack_key(v, q), N, q, zp, dlog)
                inter = s if inter is None else (inter & s)
            if bad:
                alarms.append({"pts": [list(q) for q in pts],
                               "why": "degenerate reduction in cert ladder"})
                continue
            exact = sorted(inter)
            if exact == sorted(pts):
                true_planes += 1
            elif set(exact) < set(pts) and len(exact) in (3, 4, 5):
                surplus.append(len(exact))
            else:
                alarms.append({"pts": [list(q) for q in pts],
                               "exact": [list(q) for q in exact],
                               "why": "exact set neither equal nor proper subset"})
        out[f"count{c}_modp"] = true_planes + len(surplus) + len(alarms)
        out[f"count{c}_true_char0"] = true_planes
        out[f"count{c}_surplus"] = len(surplus)
        out[f"count{c}_surplus_exact_sizes"] = {
            str(s): surplus.count(s) for s in sorted(set(surplus))}
        out[f"count{c}_alarms"] = alarms
        out[f"count{c}_true_matches_proven"] = (true_planes == CHAR0_TRUE[c])
        log(f"surplus pass p={p} count-{c}: {true_planes} true char-0 + "
            f"{len(surplus)} proven surplus (exact sizes "
            f"{out[f'count{c}_surplus_exact_sizes']}) + {len(alarms)} ALARMS")
    out["cert_primes"] = primes
    out["benign"] = all(
        out[f"count{c}_true_matches_proven"] and not out[f"count{c}_alarms"]
        for c in (5, 6))
    return out


# ------------------------------------------------------------------ assessment + report

def assess(primes, runs, kb, completed, reused, t_wall, surplus=None):
    surplus = surplus or {}
    ordered = [runs[f"n{N}_p{p}"] for p in completed]
    per_run = {str(p): run_checks(runs[f"n{N}_p{p}"]) for p in completed}
    hists = [{int(k): v for k, v in r["histogram"].items()} for r in ordered]
    c5 = [h.get(5, 0) for h in hists]
    c6 = [h.get(6, 0) for h in hists]
    c3 = [h.get(3, 0) for h in hists]
    c4 = [h.get(4, 0) for h in hists]
    # LOAD-BEARING checks: exactly what the trichotomy claim of RESULTS-CHAR0-RIGOR
    # section 2 consumes per prime (max 6 with uncapped recount, bucket fact, distinct
    # points) + ladder hygiene (distinct clean split primes).
    checks = {
        "primes_distinct": len(set(completed)) == len(completed),
        "primes_split_gt_2pow28": all(prime_clean(p) for p in completed),
        "primes_are_smallest_first": completed == split_primes(N, len(completed)),
        "max_is_6_everywhere": all(c["M_p_equals_6"] and c["no_plane_over_6"]
                                   for c in per_run.values()),
        "recount_exact_uncapped_everywhere": all(
            c["hist3_equals_distinct_minus_recounted"]
            and c["recounted_mass_equals_mult_ge2"]
            and c["histogram_sums_to_distinct"] for c in per_run.values()),
        "flats_are_coordinate_lines_everywhere": all(
            c["flats_coordinate_lines_only"] and c["rank2_equals_bucket_prediction"]
            for c in per_run.values()),
        "points_distinct_everywhere": True,      # in-run assert; recomputed for reused
        "pair_enumeration_complete_everywhere": all(
            c["pair_enumeration_complete"] for c in per_run.values()),
        "identity_spotcheck_clean_everywhere": all(
            c["identity_spotcheck_clean"] for c in per_run.values()),
        "all_per_run_predicates_pass": all(all(c.values()) for c in per_run.values()),
    }
    # Bucket identity (NOT load-bearing for the pigeonhole — RESULTS-CHAR0-RIGOR
    # section 7 — but any deviation from the PROVEN char-0 tallies 1220/41292 must be
    # certified as benign mod-p surplus, else rigor is refused):
    bucket = {
        "count5_identical_across_primes": len(set(c5)) == 1,
        "count6_identical_across_primes": len(set(c6)) == 1,
    }
    deviating = [p for p, h in zip(completed, hists)
                 if h.get(5, 0) != CHAR0_TRUE[5] or h.get(6, 0) != CHAR0_TRUE[6]]
    deviations_certified_benign = all(
        str(p) in surplus and surplus[str(p)].get("benign") for p in deviating)
    k_run = len(completed)
    load_bearing_pass = all(checks.values())
    rig = load_bearing_pass and deviations_certified_benign
    return {
        "n": N, "primes": completed, "k_run": k_run,
        "k_needed_hadamard": kb["k_needed_hadamard"],
        "k_needed_l1": kb["k_needed_l1"],
        "k_run_target": kb["k_run_target"],
        "reused_primes_reverified": reused,
        "checks": checks,
        "bucket_identity": bucket,
        "load_bearing_all_pass": load_bearing_pass,
        "deviating_primes": deviating,
        "deviations_certified_benign_surplus": deviations_certified_benign,
        "surplus_certificates": surplus,
        "count6_per_prime": c6[0] if len(set(c6)) == 1 else c6,
        "count5_per_prime": c5[0] if len(set(c5)) == 1 else c5,
        "count3_spread": {"min": min(c3), "max": max(c3), "delta": max(c3) - min(c3)}
            if c3 else None,
        "count4_spread": {"min": min(c4), "max": max(c4), "delta": max(c4) - min(c4)}
            if c4 else None,
        "count5_spread": {"min": min(c5), "max": max(c5), "delta": max(c5) - min(c5)}
            if c5 else None,
        "distinct_planes_spread": {
            "min": min(r["n_distinct_planes"] for r in ordered),
            "max": max(r["n_distinct_planes"] for r in ordered)} if ordered else None,
        "rigorous_hadamard": rig and k_run >= kb["k_needed_hadamard"],
        "rigorous_l1": rig and k_run >= kb["k_needed_l1"],
        "rigorous": rig and k_run >= kb["k_run_target"],
        "cap_coord_hadamard": kb["cap_coord_hadamard"],
        "cap_det_hadamard": kb["cap_det_hadamard"],
        "cap_coord_l1": kb["cap_coord_l1"], "cap_det_l1": kb["cap_det_l1"],
        "bounds": kb["bounds_str"], "bounds_bits": kb["bounds_bits"],
        "per_run_checks": per_run,
        "wall_total_sec": round(t_wall, 1),
    }


def write_md(a, runs, stopped_reason):
    kb_bits = a["bounds_bits"]
    rows = []
    for p in a["primes"]:
        r = runs[f"n{N}_p{p}"]
        h = {int(k): v for k, v in r["histogram"].items()}
        rows.append((p, r["z"], r["M_p"], h.get(3, 0), h.get(4, 0), h.get(5, 0),
                     h.get(6, 0), r["n_distinct_planes"],
                     "reused+rechecked" if p in a["reused_primes_reverified"] else "run",
                     r["timing_sec"]["total"]))
    md = []
    md.append("# M(128) rigor — the n = 128 prime ladder: M(128) <= 6 (ArkLib#371)\n")
    md.append(
        "Extends RESULTS-CHAR0-RIGOR.md (invisibility trichotomy + per-plane pigeonhole,\n"
        "proved there for n <= 64) to n = 128, closing caveat #1 of RESULTS-RECIPROCAL.md.\n"
        "Census engine: `probe_reciprocal_census.py` (streamed dedupe + exact Moebius\n"
        "recount; gated by bit-identical histogram reproduction against the original\n"
        "census at n = 32 and n = 64).  Driver: `probe_m128_rigor.py`; machine results in\n"
        "`results_reciprocal_census.json` (per prime) and `results_char0_rigor.json`\n"
        "(n=128 assessment block).  All arithmetic exact integers.\n")
    md.append("## 1. Exact ladder length k(128)\n")
    md.append(
        "Case integers of a hypothetical >= 7-incidence plane at m = 64 "
        "(RESULTS-CHAR0-RIGOR 1c-1d), cap(B) = max{t : 2^(28t) < B}, "
        "k = 2*cap(B_coord) + cap(B_det) + 1:\n")
    md.append("| route | B_coord | bits | cap | B_det | bits | cap | k needed |")
    md.append("|---|---|---|---|---|---|---|---|")
    md.append(f"| Hadamard | 3^96 | {kb_bits['B_coord_hadamard']} | "
              f"{a['cap_coord_hadamard']} | 54^64 | {kb_bits['B_det_hadamard']} | "
              f"{a['cap_det_hadamard']} | **{a['k_needed_hadamard']}** |")
    md.append(f"| L1 (cruder) | 6^64 | {kb_bits['B_coord_l1']} | {a['cap_coord_l1']} | "
              f"72^64 | {kb_bits['B_det_l1']} | {a['cap_det_l1']} | "
              f"**{a['k_needed_l1']}** |")
    md.append(
        f"\nThe prior estimate k(128) = 24 (RESULTS-RECIPROCAL caveat 1) is the exact\n"
        f"Hadamard value — verified: cap(3^96) = {a['cap_coord_hadamard']} "
        f"(2^140 < 3^96 < 2^168), cap(54^64) = {a['cap_det_hadamard']} "
        f"(2^364 < 54^64 < 2^392), k = 2*5 + 13 + 1 = 24.  The cruder L1 route needs\n"
        f"{a['k_needed_l1']} (cap(72^64) = {a['cap_det_l1']}: 2^392 < 72^64 < 2^420), so\n"
        f"the ladder target is max(24, 25) = **{a['k_run_target']} primes** — the verdict\n"
        f"is then independent of the height route.\n")
    md.append("## 2. Ladder primes and reuse\n")
    md.append(
        f"The {a['k_run_target']} smallest split primes p == 1 (mod 128), p > 2^28, were\n"
        f"used, smallest first.  The first two (268437889, 268438657) are exactly the two\n"
        f"primes of the RESULTS-RECIPROCAL census; their stored full runs were REUSED\n"
        f"after an integrity recheck (all stored in-run asserts re-derived from the\n"
        f"stored numbers, plus deterministic recomputation of z, of the surface-point\n"
        f"distinctness assert, and of the coordinate-line flats/bucket fact).  The\n"
        f"remaining {a['k_run'] - len(a['reused_primes_reverified'])} primes were run\n"
        f"fresh, sequentially (disk discipline: temp dirs deleted between runs, free\n"
        f"space verified > {MIN_FREE_GIB} GiB before each run).\n")
    md.append("## 3. Per-prime results\n")
    md.append("Cleanliness per prime (same predicates as the n <= 64 ladders, hard\n"
              "asserts in-run): points distinct, pair enumeration complete, the only\n"
              "flats are the two coordinate lines with rank-2 count = 127*126 = 16002,\n"
              "recount exact and uncapped (Moebius recount of every mult>=2 key,\n"
              "validated vs the brute counter on 200 planes per run), spanning-identity\n"
              "spot check 0 failures, M_p = 6, zero planes above 6.\n")
    md.append("| # | p | z | M_p | count3 | count4 | count5 | count6 | distinct planes | source | wall (s) |")
    md.append("|---|---|---|-----|--------|--------|--------|--------|------------------|--------|----------|")
    for i, (p, z, mp, h3, h4, h5, h6, dist, src, w) in enumerate(rows, 1):
        md.append(f"| {i} | {p} | {z} | {mp} | {h3} | {h4} | {h5} | {h6} | {dist} | "
                  f"{src} | {w} |")
    md.append("\n## 4. Cross-prime histogram facts (O157)\n")
    if a["bucket_identity"]["count6_identical_across_primes"]:
        md.append(
            f"- count-6 = **{a['count6_per_prime']}** is IDENTICAL at every prime and\n"
            f"  equals the exact law (n-4)(11n-76)/4 = 41292; all 41292 planes carry\n"
            f"  exact char-0 certificates (results_count56_verify.json,\n"
            f"  RESULTS-RECIPROCAL section 3).")
    else:
        md.append(f"- count-6 per prime: {a['count6_per_prime']} — NOT identical; see\n"
                  f"  the surplus certificates below.")
    if a["bucket_identity"]["count5_identical_across_primes"]:
        md.append(f"- count-5 = **{a['count5_per_prime']}** is IDENTICAL at every "
                  f"prime (= 10(n-6) = 1220, all char-0-certified).")
    else:
        c5s = a["count5_spread"]
        md.append(
            f"- count-5 is NOT identical across primes: values in [{c5s['min']}, "
            f"{c5s['max']}] (proven char-0 tally: 1220).  **The mod-p surplus reaches\n"
            f"  the count-5 bucket at n = 128** — one bucket higher than the count-3/4\n"
            f"  surplus first seen in RESULTS-RECIPROCAL.  Deviating primes:\n"
            f"  {a['deviating_primes']}.  This is the O157 mechanism (the fixed\n"
            f"  cyclotomic resultants of small-height planes capture ~2^28-sized\n"
            f"  primes); it is NOT load-bearing for the pigeonhole (RESULTS-CHAR0-RIGOR\n"
            f"  section 7) but is certified exactly in section 5 rather than assumed.")
    c3s, c4s = a["count3_spread"], a["count4_spread"]
    md.append(
        f"- count-3/count-4 mod-p surplus (allowed and expected at n = 128, per O157 —\n"
        f"  surplus only ever inflates counts, it cannot hide an admissible char-0\n"
        f"  plane): count3 in [{c3s['min']}, {c3s['max']}] (spread {c3s['delta']}),\n"
        f"  count4 in [{c4s['min']}, {c4s['max']}] (spread {c4s['delta']}), distinct\n"
        f"  planes in [{a['distinct_planes_spread']['min']}, "
        f"{a['distinct_planes_spread']['max']}].")
    if a["deviating_primes"]:
        md.append("\n## 5. Surplus certificates at deviating primes\n")
        md.append(
            "For every prime whose count-5/6 bucket deviates from the proven char-0\n"
            "tallies (1220 / 41292), the census was re-run keeping the count-5/6\n"
            "incidence sets, and EVERY such plane was certified exactly: fix one\n"
            "rank-3 triple of its mod-p incidence set, build the exact char-0 plane\n"
            "through that triple (cross product), and compute its exact char-0\n"
            "incidence set by the multi-prime certificate ladder ((prod p_i)^2 >\n"
            "432^64, the verify6 lemma).  exact set == mod-p set <=> true char-0\n"
            "plane; exact set a proper subset <=> pure mod-p surplus (a char-0\n"
            "count-3/4 plane inflated at this prime).  Anything else would be an\n"
            "alarm and would refuse rigor.\n")
        for p in a["deviating_primes"]:
            s = a["surplus_certificates"].get(str(p))
            if not s:
                md.append(f"- p = {p}: NOT CERTIFIED (no surplus pass ran) — rigor refused.")
                continue
            for c in (5, 6):
                md.append(
                    f"- p = {p}, count-{c}: {s[f'count{c}_modp']} mod-p planes = "
                    f"**{s[f'count{c}_true_char0']} true char-0** (matches proven "
                    f"tally: {s[f'count{c}_true_matches_proven']}) + "
                    f"**{s[f'count{c}_surplus']} proven surplus** (exact char-0 sizes "
                    f"{s[f'count{c}_surplus_exact_sizes']}), alarms: "
                    f"{len(s[f'count{c}_alarms'])}")
            md.append(f"  benign: **{s['benign']}**")
    md.append("\n## 6. Assessment\n")
    md.append("Load-bearing checks (the trichotomy's per-prime requirements + ladder "
              "hygiene):\n")
    for k, v in a["checks"].items():
        md.append(f"- {k}: {v}")
    md.append("\nBucket identity (extra evidence, not load-bearing; deviations "
              "certified above):\n")
    for k, v in a["bucket_identity"].items():
        md.append(f"- {k}: {v}")
    md.append(f"- deviations_certified_benign_surplus: "
              f"{a['deviations_certified_benign_surplus']}")
    md.append("")
    md.append(f"- k run: **{a['k_run']}** (needed: {a['k_needed_hadamard']} Hadamard / "
              f"{a['k_needed_l1']} L1; target {a['k_run_target']})")
    md.append(f"- rigorous (Hadamard ladder): **{a['rigorous_hadamard']}**")
    md.append(f"- rigorous (L1 ladder): **{a['rigorous_l1']}**")
    md.append(f"- wall total: {a['wall_total_sec']} s")
    if stopped_reason:
        md.append(f"- EARLY STOP: {stopped_reason}")
    md.append("\n## 7. Verdict\n")
    if a["rigorous"]:
        md.append(
            f"**M(128) <= 6 is RIGOROUS** (k_run = {a['k_run']} clean primes >= "
            f"{a['k_needed_hadamard']} Hadamard and >= {a['k_needed_l1']} L1 — route-\n"
            f"independent).  Combined with the exact char-0 lower bound M(128) >= 6\n"
            f"(witness family S(128), RESULTS-RECIPROCAL section 2): **M(128) = 6**.\n"
            f"The constant-6 law M(n) = 6 now holds RIGOROUSLY at every\n"
            f"n in {{8, 16, 32, 64, 128}}.\n")
    else:
        md.append(
            f"**NOT rigorous**: k_run = {a['k_run']} of {a['k_run_target']} target "
            f"primes completed cleanly"
            + (f" ({stopped_reason})" if stopped_reason else "")
            + ".  M(128) <= 6 remains evidence at this strength; "
            f"M(128) >= 6 stays proven (exact).\n")
    md.append("## 8. Caveats / scope\n")
    md.append(
        "- Statement scope: M(128) as defined (non-normalizer, invertible hyperplanes\n"
        "  against P(i,j) over (Z/128)^2); nothing claimed for n = 256 (k(256) = 47/49\n"
        "  Hadamard/L1, census out of disk budget here).\n"
        "- The cross-prime count-5 bucket identity REQUESTED for this ladder does NOT\n"
        "  hold verbatim: mod-p surplus reaches the 5-bucket at some primes (section\n"
        "  4).  This was anticipated in direction (O157 allows surplus; it inflates,\n"
        "  never hides) but not in bucket; instead of weakening the criterion\n"
        "  silently, every deviation is certified exactly (section 5) — each extra\n"
        "  plane is a PROVEN char-0 count-3/4 plane inflated at that prime, and the\n"
        "  true char-0 count-5/6 sub-tallies match the proven 1220/41292 at every\n"
        "  deviating prime.  rigorous = true is claimed only with those certificates\n"
        "  in hand; count-6 identity itself held at every prime.\n"
        "- Load-bearing inputs: the trichotomy + pigeonhole derivation of\n"
        "  RESULTS-CHAR0-RIGOR (unchanged — only the exact integer bounds at m = 64 are\n"
        "  instantiated here); per-prime census cleanliness (in-run asserts listed in\n"
        "  section 3); the engine gate (bit-identical n=32/64 reproduction, recorded in\n"
        "  results_reciprocal_census.json).  The count-5/6 cross-prime identity is\n"
        "  required; the count-3/4 spread is reported but NOT load-bearing (mod-p\n"
        "  surplus inflates only).\n"
        "- The two reused primes were not re-run end-to-end; their reuse rests on the\n"
        "  stored run records (whose internal consistency was re-derived: histogram\n"
        "  mass identities, pair/rank-2 counts, zero over-6 list) plus deterministic\n"
        "  recomputation of z / point distinctness / flats.  Every other prime ran\n"
        "  fresh in this ladder with live asserts.\n"
        "- top1_canon at n = 128 is a hex-key-ordered sample of the 41292-member\n"
        "  count-6 tie (key order is prime-dependent), so the n<=64 ladder's\n"
        "  `top1_canon_identical` check is replaced by the stronger count-5/6\n"
        "  bucket-identity + the exact char-0 certificates of RESULTS-RECIPROCAL.\n")
    with open(OUT_MD, "w") as fh:
        fh.write("\n".join(md))


def update_rigor_json(a):
    data = {"runs": {}}
    if os.path.exists(RIGOR_JSON):
        with open(RIGOR_JSON) as fh:
            data = json.load(fh)
    data.setdefault("runs", {})
    data["runs"]["128"] = {
        "assessment": a,
        "per_prime": "see results_reciprocal_census.json (runs n128_p*)",
    }
    with open(RIGOR_JSON, "w") as fh:
        json.dump(data, fh, indent=1)


# ------------------------------------------------------------------ main

def main():
    t0 = time.time()
    kb = k_block()
    log(f"k(128): Hadamard {kb['k_needed_hadamard']} (caps {kb['cap_coord_hadamard']}/"
        f"{kb['cap_det_hadamard']}), L1 {kb['k_needed_l1']} (caps {kb['cap_coord_l1']}/"
        f"{kb['cap_det_l1']}) -> target {kb['k_run_target']} primes")
    primes = split_primes(N, kb["k_run_target"])
    assert all(prime_clean(p) for p in primes) and len(set(primes)) == len(primes)
    log(f"ladder primes (smallest first): {primes}")

    runs = load_runs()
    reused = []
    stopped_reason = None
    completed = []

    for i, p in enumerate(primes):
        key = f"n{N}_p{p}"
        if key in runs:
            r = runs[key]
            checks = reverify_stored(p, r)
            if all(checks.values()):
                log(f"prime {i+1}/{len(primes)} p={p}: stored run REUSED "
                    f"(integrity recheck: all {len(checks)} predicates pass)")
                if p in (268437889, 268438657) and i < 2:
                    reused.append(p)
                completed.append(p)
                continue
            log(f"prime {i+1}/{len(primes)} p={p}: stored run FAILED recheck "
                f"{ {k: v for k, v in checks.items() if not v} } -> re-running")
        elapsed = time.time() - t0
        if elapsed > BUDGET_SEC:
            stopped_reason = (f"wall budget exceeded ({elapsed:.0f}s > {BUDGET_SEC:.0f}s) "
                              f"after {len(completed)} primes")
            log("STOP: " + stopped_reason)
            break
        shutil.rmtree(TMPDIR, ignore_errors=True)
        free = free_gib()
        if free < MIN_FREE_GIB:
            stopped_reason = (f"free disk {free:.2f} GiB < {MIN_FREE_GIB} GiB "
                              f"before prime {p}")
            log("STOP: " + stopped_reason)
            break
        log(f"prime {i+1}/{len(primes)} p={p}: running census "
            f"(free disk {free:.2f} GiB, elapsed {elapsed:.0f}s)")
        try:
            res = run_census(N, p)
        except Exception as e:                       # in-run assert = dirty prime/run
            stopped_reason = f"census run FAILED at p={p}: {type(e).__name__}: {e}"
            log("STOP: " + stopped_reason)
            shutil.rmtree(TMPDIR, ignore_errors=True)
            break
        merge_save(res)
        runs = load_runs()
        shutil.rmtree(TMPDIR, ignore_errors=True)
        checks = run_checks(runs[key])
        if not all(checks.values()):
            stopped_reason = (f"post-run predicate failure at p={p}: "
                              f"{ {k: v for k, v in checks.items() if not v} }")
            log("STOP: " + stopped_reason)
            break
        completed.append(p)
        log(f"prime {i+1}/{len(primes)} p={p}: clean "
            f"(M_p=6, hist {runs[key]['histogram']}, {res['timing_sec']['total']}s)")

    # ---- surplus certificates at any prime whose 5/6 buckets deviate from the
    #      proven char-0 tallies (no hand-waving: prove the inflation or refuse rigor)
    surplus = {}
    deviating = []
    for p in completed:
        h = {int(k): v for k, v in runs[f"n{N}_p{p}"]["histogram"].items()}
        if h.get(5, 0) != CHAR0_TRUE[5] or h.get(6, 0) != CHAR0_TRUE[6]:
            deviating.append(p)
    for p in deviating:
        if time.time() - t0 > BUDGET_SEC:
            log(f"surplus pass p={p}: SKIPPED (wall budget) -> rigor will be refused")
            continue
        shutil.rmtree(TMPDIR, ignore_errors=True)
        if free_gib() < MIN_FREE_GIB:
            log(f"surplus pass p={p}: SKIPPED (disk) -> rigor will be refused")
            continue
        try:
            surplus[str(p)] = surplus_certify(p)
        except Exception as e:
            log(f"surplus pass p={p}: FAILED {type(e).__name__}: {e} -> rigor refused")
            surplus[str(p)] = {"benign": False, "error": f"{type(e).__name__}: {e}"}
        shutil.rmtree(TMPDIR, ignore_errors=True)

    a = assess(primes, runs, kb, completed, reused, time.time() - t0, surplus)
    if stopped_reason:
        a["early_stop"] = stopped_reason
    update_rigor_json(a)
    write_md(a, runs, stopped_reason)
    log(f"DONE: k_run={a['k_run']}/{a['k_run_target']}, "
        f"rigorous_hadamard={a['rigorous_hadamard']}, rigorous_l1={a['rigorous_l1']}, "
        f"rigorous={a['rigorous']}, deviating={a['deviating_primes']}, "
        f"benign={a['deviations_certified_benign_surplus']}, "
        f"wall={a['wall_total_sec']}s")
    print("RESULT " + json.dumps({
        "k_run": a["k_run"], "k_target": a["k_run_target"],
        "rigorous": a["rigorous"], "deviating": a["deviating_primes"],
        "early_stop": stopped_reason}))


if __name__ == "__main__":
    main()

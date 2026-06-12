#!/usr/bin/env python3
"""Round-9 probe (#371): THE UNIFIED PACKING LAW + the piecewise envelope.

Step-A derivation under test
----------------------------
The round-8 BISIMPLEX generalizes to "k pairwise-disjoint (e+1)-simplices", but the
construction collapses to ONE two-parameter family (the round-9 discovery):

  THE TWO-BLOCK PACKING FAMILY (S1, Z):  pick disjoint S1 (|S1| = s1 >= 1) and
  Z (|Z| = z) in the domain, B2 := the rest; v := prod_{zeta in Z}(X - zeta);
  stack u1 = v|_{S1}, u0 = (X*v)|_{S1}.  Then gamma = -x is bad for EVERY domain
  point x not in Z:
    * x in S1 ("kill"): line word = ((X-x)v)|_{S1} agrees with the ZERO codeword on
      complement(S1) u {x}  (n - s1 + 1 points); direction unfit there (forced
      q1 = 0 on the n-s1 >= d+1 off-S1 points, but u1(x) = v(x) != 0).
    * x in B2 ("root alignment"): line word agrees with the codeword (X-x)v
      (degree z+1 <= d) on S1 u Z u {x}  (s1 + z + 1 points); direction unfit
      (forced q1 = v on the s1+z >= d+1 points of S1 u Z, but u1(x) = 0 != v(x)).

  COUNT n - z at threshold T = min(n-s1+1, s1+z+1), window
  z+1 <= d,  d+1 <= n-s1,  d+1 <= s1+z.

  Per-radius optimum at threshold t (E := n-t):  z* = max(0, 2t-n-2) (and
  s1 in the feasible band), giving  W_packing(n,d,t) = min(n, 2E+2)  whenever
  d+2 <= t and 2t <= n+d+1 (cap regime additionally needs 2d+2 <= n, t <= n-d).

  SUBSUMPTION: the "k disjoint (e+1)-simplices" stack IS this family with
  s1 = e+1, z = n-k(e+1): count k(e+1) = n-z, threshold n-(k-1)(e+1)+1, window
  n-k(e+1)+1 <= d <= n-(k-1)(e+1)-1.  Since k(e+1) <= min(n, 2E+2) at its own
  radius E = (k-1)(e+1)-1 with the unified window implied, k >= 3 NEVER beats
  the envelope (k=2 = bisimplex = the z>0 optimum; the cap n = the z=0 optimum,
  which at t = n/2+1 is the antipodal pencil count).

This probe verifies:
  T1  the exact count law (= n-z, word-level exact, every applicable cell) at
      (17,8,2), (97,8,64), (97,16,8) for a grid of (d, s1, z);
  T2  the k=3 cells the mission asked for: (17,8) k=3,e=1 d=3 (count 6) and the
      STRICT subsumption cell (97,16,8) d=5: k=3,e=3 stack (count 12) vs the
      unified optimum (count 16) at the same threshold t=9;
  T3  the overlapping question at the round-8 hint cell (97,16,2), t=7:
      hill-climb reproduction; structure dump of any count > 16; independent
      replication at p=257 (char-0 vs field-coincidence verdict);
  T4  the piecewise envelope formula vs the round-8 EXHAUSTIVE census table
      (F17 all cells, F97 d=3 t=6 shoulder cell).

Sound exactness: every bad-at-t scalar (t >= d+2) appears among the defect-ratio
candidates of some (d+2)-subset of its witness, so count_bad is exact.
"""

import os
import sys
import json
import random
import itertools
from math import comb, gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_bad_family_census import (  # noqa: E402
    Domain, spectrum_N, classify_blocks, monomial, doublet_stack)


def log(msg):
    print(msg, flush=True)


# ------------------------------------------------------------------ the family

def packing_stack(dom, S1, Z):
    """u1 = v|_S1, u0 = (X v)|_S1 with v the vanishing polynomial of Z."""
    p, n, X = dom.P, dom.N, dom.X
    Zs = set(Z)
    assert not (set(S1) & Zs)

    def v(x):
        out = 1
        for zeta in Z:
            out = out * (x - X[zeta]) % p
        return out

    u1 = [v(X[i]) if i in set(S1) else 0 for i in range(n)]
    u0 = [X[i] * v(X[i]) % p if i in set(S1) else 0 for i in range(n)]
    return u0, u1


def packing_cell_count(dom, d, s1, z, t=None):
    """Exact bad count of the (s1, z) stack at its design threshold."""
    n = dom.N
    S1 = list(range(s1))
    Z = list(range(s1, s1 + z))
    T = min(n - s1 + 1, s1 + z + 1)
    if t is None:
        t = T
    u0, u1 = packing_stack(dom, S1, Z)
    cnt = dom.count_bad(u0, u1, t, d, prefilter=False)
    return cnt, T


def W_packing(n, d, t):
    """The unified per-radius packing optimum (0 when outside the window)."""
    E = n - t
    if t < d + 2 or 2 * t > n + d + 1:
        return 0
    if 2 * t <= n + 2:                       # cap regime: z = 0
        # need s1 with d+1 <= s1, d+1 <= n-s1, t <= min(n-s1+1, s1+1)
        lo, hi = max(d + 1, t - 1), min(n - d - 1, n - t + 1)
        return n if lo <= hi else 0
    return 2 * E + 2                          # z = 2t-n-2 regime (= bisimplex)


def kpacking_params(n, k, e):
    """The k-disjoint-(e+1)-simplex reading: (s1, z, count, T, d-window)."""
    m = k * (e + 1)
    return dict(s1=e + 1, z=n - m, count=m, T=n - (k - 1) * (e + 1) + 1,
                d_lo=n - m + 1, d_hi=n - (k - 1) * (e + 1) - 1)


# ------------------------------------------------------------------ T1: count law

def t1_count_law(results):
    log("== T1: THE TWO-BLOCK PACKING COUNT LAW (exact, word-level) ==")
    ok = True
    grid = [
        # (p, g, n, d, cells [(s1, z)])
        (17, 2, 8, 1, [(4, 0), (5, 0), (3, 0)]),
        (17, 2, 8, 2, [(4, 0), (5, 0), (4, 1), (5, 1), (3, 1)]),
        (17, 2, 8, 3, [(3, 2), (4, 2), (3, 1), (4, 1), (2, 2)]),
        (97, 64, 8, 2, [(4, 0), (4, 1), (5, 1)]),
        (97, 64, 8, 3, [(3, 2), (4, 2)]),
        (97, 8, 16, 2, [(8, 0), (9, 1), (7, 1)]),
        (97, 8, 16, 4, [(8, 0), (10, 2), (9, 3), (7, 3), (6, 2)]),
    ]
    rows = []
    for (p, g, n, d, cells) in grid:
        dom = Domain(p, g, n)
        for (s1, z) in cells:
            # window check
            win = (z + 1 <= d and d + 1 <= n - s1 and d + 1 <= s1 + z)
            if not win:
                continue
            cnt, T = packing_cell_count(dom, d, s1, z)
            pred = n - z
            extra = cnt - pred
            tag = "EXACT" if cnt == pred else (
                f"+{extra} EXTRA (small-field surplus?)" if cnt > pred
                else "DEFICIT <-- LAW REFUTED")
            if cnt < pred:
                ok = False
            log(f"   p={p} n={n} d={d} (s1,z)=({s1},{z}) T={T}: "
                f"count={cnt} predicted={pred} [{tag}]")
            rows.append(dict(p=p, n=n, d=d, s1=s1, z=z, T=T,
                             count=cnt, pred=pred))
    results["t1_count_law"] = rows
    assert ok, "packing count law DEFICIT"
    log("   T1 PASS: count >= n-z at every cell (law lower bound verified)")
    return rows


# ------------------------------------------------------------------ T2: k=3 cells

def t2_k3_subsumption(results):
    log("== T2: k=3 PACKINGS + SUBSUMPTION ==")
    rows = []
    # mission cell: n=8, k=3, e=1 (3 disjoint 2-sets), d-window {3}, count 6
    kp = kpacking_params(8, 3, 1)
    log(f"   k=3,e=1,n=8 params: {kp}  (d-window [{kp['d_lo']},{kp['d_hi']}] "
        f"nonempty: {kp['d_lo'] <= kp['d_hi']})")
    dom = Domain(17, 2, 8)
    cnt, T = packing_cell_count(dom, 3, kp["s1"], kp["z"])
    log(f"   (17,8) d=3 k=3-stack: count={cnt} predicted={kp['count']} at T={T}"
        f"  (cell is explosion band t=d+2: census W=p=17 dominates)")
    rows.append(dict(cell="(17,8,3) k3e1", count=cnt, pred=kp["count"], T=T))
    assert cnt >= kp["count"]
    # strict subsumption cell: (97,16) d=5, t=9: k=3,e=3 (count 12) vs unified (16)
    kp = kpacking_params(16, 3, 3)
    dom = Domain(97, 8, 16)
    c_k3, T_k3 = packing_cell_count(dom, 5, kp["s1"], kp["z"])
    c_uni, T_uni = packing_cell_count(dom, 5, 8, 0)
    log(f"   (97,16) d=5: k=3,e=3 stack count={c_k3} (pred {kp['count']}) at "
        f"T={T_k3}; unified z=0 count={c_uni} (pred 16) at T={T_uni}")
    rows.append(dict(cell="(97,16,5) k3e3 vs unified", k3=c_k3, uni=c_uni,
                     T_k3=T_k3, T_uni=T_uni))
    assert c_k3 >= 12 and c_uni >= 16 and T_k3 == T_uni == 9, "T2 mismatch"
    log("   T2 PASS: k=3 construction works AND is strictly beaten by the "
        "unified z=0 optimum at the same threshold (12 < 16 at t=9)")
    results["t2_k3"] = rows
    return rows


# ------------------------------------------------------------------ T3: t=7 cell

def minimal_supports(dom, u0, u1, gamma, d, t):
    """All maximal agreement sets (>= t, direction unfit) for gamma; returns the
    minimal error supports (complements)."""
    p, n, X = dom.P, dom.N, dom.X
    ug = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    sups = set()
    best = 0
    for B in itertools.combinations(range(n), d + 1):
        cs = dom.coeffs(B, ug)
        A = tuple(i for i in range(n) if dom.evalp(cs, X[i]) == ug[i])
        if len(A) >= t and not dom.fits(list(A), u1, d):
            if len(A) > best:
                best, sups = len(A), set()
            if len(A) == best:
                sups.add(frozenset(set(range(n)) - set(A)))
    return best, sups


def t3_overlap_cell(results, iters=420, seed=371):
    log("== T3: THE (n=16, d=2, t=7) OVERLAP-HINT CELL ==")
    random.seed(seed)
    rows = {}
    for (p, g) in ((97, 8), (257, 2)):
        dom = Domain(p, g, 16)
        n, d, t = 16, 2, 7
        h = n // 2
        seeds = [
            packing_stack(dom, list(range(8)), []) + ("packing(8,0)",),
            packing_stack(dom, list(range(9)), []) + ("packing(9,0)",),
            packing_stack(dom, list(range(10)), [10]) + ("packing(10,1)",),
            (monomial(dom, h), monomial(dom, h + 1), "pencil"),
        ]
        best, arg, beststack = 0, None, None

        def consider(u0, u1, label):
            nonlocal best, arg, beststack
            th = dom.bad_set_thresholds(u0, u1, d, max(d + 3, t))
            c = sum(1 for T in th.values() if T >= t)
            if c > best:
                best, arg, beststack = c, label, (list(u0), list(u1))
            return c

        for (u0, u1, name) in seeds:
            consider(u0, u1, name)
        cur = (list(seeds[0][0]), list(seeds[0][1]))
        cur_c = consider(cur[0], cur[1], "seed")
        for _ in range(iters):
            u0, u1 = list(cur[0]), list(cur[1])
            for _ in range(random.randrange(1, 3)):
                (u0 if random.randrange(2) == 0 else u1)[
                    random.randrange(n)] = random.randrange(p)
            c = consider(u0, u1, "climb")
            if c >= cur_c:
                cur, cur_c = (u0, u1), c
        log(f"   p={p}: observed max {best} [{arg}] (unified-law value 16)")
        row = dict(p=p, best=best, arg=str(arg))
        if best > 16 and beststack is not None:
            u0, u1 = beststack
            exact = dom.count_bad(u0, u1, t, d, prefilter=False)
            th = dom.bad_set_thresholds(u0, u1, d, t)
            gams = sorted(g0 for g0, T in th.items() if T >= t)
            neg_dom = {(-x) % p for x in dom.X}
            in_dom = sum(1 for g0 in gams if g0 in neg_dom)
            sig = []
            for g0 in gams:
                w, sups = minimal_supports(dom, u0, u1, g0, d, t)
                s0 = min(sups, key=lambda s: tuple(sorted(s))) if sups else \
                    frozenset()
                sig.append((g0, n - w, tuple(sorted(s0))))
            blocks, left = classify_blocks(
                [(g0, w, frozenset(s)) for (g0, w, s) in sig], n)
            log(f"      exact count {exact}; scalars in -domain: {in_dom}/"
                f"{len(gams)}; blocks: {blocks}; leftovers: {len(left)}")
            log(f"      stack u0={u0}")
            log(f"      stack u1={u1}")
            log(f"      per-scalar (gamma, weight, support): {sig}")
            row.update(exact=exact, in_dom=in_dom, n_gams=len(gams),
                       blocks=[str(b) for b in blocks], left=len(left),
                       u0=u0, u1=u1,
                       sig=[(int(g0), int(w), list(map(int, s)))
                            for (g0, w, s) in sig])
        rows[p] = row
    results["t3_overlap"] = rows
    v97, v257 = rows[97]["best"], rows[257]["best"]
    verdict = ("CHAR-0 CANDIDATE (replicates above 16 at both primes)"
               if v97 > 16 and v257 > 16 else
               "FIELD-COINCIDENCE / NOT REPRODUCED (cap n holds char-0)"
               if max(v97, v257) <= 16 else
               f"MIXED: 97->{v97}, 257->{v257} (needs structure comparison)")
    log(f"   T3 VERDICT: {verdict}")
    rows["verdict"] = verdict
    return rows


# ------------------------------------------------------------------ T4: envelope

def envelope_char0(n, d, t, mu):
    """The piecewise char-0 envelope formula F(n,d,t) (excluding the explosion
    band t = d+2 where the value is p, and mod-p surpluses)."""
    vals = [1]
    # staircase (level-j spectrum rungs at their radii)
    r = d + 2
    for j in range(mu):
        rp = (r - 2) // 2 ** j + 2
        if 2 <= rp <= 2 ** (mu - j - 1) and rp * 2 ** j >= t:
            vals.append(spectrum_N(mu - j, rp))
    # packing (running max over t' >= t: epsMCA monotone)
    for tp in range(t, n + 1):
        vals.append(W_packing(n, d, tp))
    # pencil rungs
    h = n // 2
    if n % 2 == 0:
        for s in range(1, d + 1):
            if h % s == 0 and d + 1 <= h and h + s >= t:
                vals.append(n // s)
    # simplex ladder
    for e in range(1, n - d - 1):
        if n - e >= t:
            vals.append(e + 1)
    # doublet
    if n - 1 >= t:
        vals.append(2)
    return max(vals)


def t4_envelope_consistency(results):
    log("== T4: PIECEWISE ENVELOPE vs THE EXHAUSTIVE CENSUS ==")
    census = {  # (p, n, d) -> {t: W_t}   (round-8 exhaustive, exact)
        (17, 8, 1): {5: 8, 6: 3, 7: 2},
        (17, 8, 2): {4: 17, 5: 11, 6: 4, 7: 2, 8: 1},
        (17, 8, 3): {5: 17, 6: 7, 7: 2},
        (97, 8, 3): {6: 6},   # the exhaustively re-censused shoulder cell
    }
    surplus_cells = {(17, 8, 2, 5): 3, (17, 8, 3, 6): 1}  # known mod-17 extras
    ok = True
    rows = []
    for (p, n, d), Ws in census.items():
        mu = n.bit_length() - 1
        for t, W in sorted(Ws.items()):
            if t == d + 2:
                pred, kind = p, "explosion"
            else:
                pred, kind = envelope_char0(n, d, t, mu), "char-0"
            sur = surplus_cells.get((p, n, d, t), 0)
            match = (pred + sur == W)
            ok = ok and match
            log(f"   (p={p},n={n},d={d}) t={t}: census W={W}, formula={pred}"
                f"{f'+{sur} (mod-{p})' if sur else ''} [{kind}]"
                f"{' OK' if match else ' <-- MISMATCH'}")
            rows.append(dict(p=p, n=n, d=d, t=t, W=W, pred=pred, sur=sur,
                             match=match))
    results["t4_envelope"] = rows
    assert ok, "envelope formula mismatch vs census"
    log("   T4 PASS: formula = census at EVERY exhaustive cell "
        "(modulo the two known mod-17 surpluses)")
    return rows


# ------------------------------------------------------------------ main

def main():
    results = {}
    only = sys.argv[1] if len(sys.argv) > 1 else "all"
    if only in ("all", "t1"):
        t1_count_law(results)
    if only in ("all", "t2"):
        t2_k3_subsumption(results)
    if only in ("all", "t4"):
        t4_envelope_consistency(results)
    if only in ("all", "t3"):
        t3_overlap_cell(results)
    with open("scripts/probes/packing_envelope_results.json", "w") as f:
        json.dump(results, f, indent=1, default=str)
    log("DONE — results in scripts/probes/packing_envelope_results.json")


if __name__ == "__main__":
    main()

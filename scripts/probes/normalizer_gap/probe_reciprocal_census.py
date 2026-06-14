#!/usr/bin/env python3
"""
probe_reciprocal_census.py -- ArkLib#371: extended census WITHIN the reciprocal family
at n = 128 (task 3 of the BS-reciprocal-branch cycle).

WHY THIS IS THE RECIPROCAL CENSUS.  probe_reciprocal_param.py proves (exact ring
identity, machine-verified exhaustively at n=8 and randomly at 16..256):
    rev(cross(P00, P(i1,j1), P(i2,j2))) = zeta^Sigma * conj(same),  Sigma = i1+j1+i2+j2,
i.e. EVERY plane spanned by a rank-3 triple of surface points through P(0,0) is
conjugate-reciprocal with lambda = zeta^{-Sigma}.  Since every plane with incidence
count >= 3 (rank-3 incidence set) IS spanned by such a triple, the "restrict the census
to reciprocal planes" filter passes every census candidate: the reciprocal census IS the
census.  (The filter is also provably invisible to single-evaluation mod-p data --
V5 of probe_reciprocal_param.py -- so there is no cheaper reciprocal-only enumeration
at one embedding.)  This run still spot-checks the identity mod p in-loop.

ENGINE (independent reimplementation of the dedupe + recount paths, addressing the
O156 census-debt note; gated by exact histogram reproduction at n = 32, 64):
  pass 1   6 worker processes enumerate all pairs (Q, R), Q < R, of non-P00 surface
           points; cross-product normal; identical skip logic to the original census
           (rank-2 / normalizer-pattern / singular); normalized keys are STREAMED to
           gzip files (never materialized in RAM -- the previous in-RAM probe OOM'd).
  dedupe   zcat | LC_ALL=C sort (disk temps, compressed) | uniq -c | awk filter:
           exact multiplicities; mult-1 keys are count-3 planes (proven lemma);
           mult >= 2 keys go to recount.
  recount  Moebius O(n) exact count per candidate plane (z^j = -(v2 z^i + v3)/(v0 z^i
           + v1) must land in <z>), batched modular inversion; verified in-run against
           the brute O(n^2) count on a sample.  den == 0 forces num != 0 (else the
           plane is singular -- asserted).
Histogram = {3: distinct - #cands} + exact recounts.  M_p = max count (flats checked
separately, as in the original census: the only rank-2 flats are the two coordinate
lines and their pencils are identically singular).

Direction of evidence (stated carefully): reduction mod a split prime PRESERVES char-0
incidences, so for any char-0 plane that stays admissible mod p, its mod-p count >= its
char-0 count (surplus inflates, never deflates).  Hence mod-p max = 6 bounds char-0
planes VISIBLE at p; a char-0 plane with count >= 7 could still be INVISIBLE at p if p
divides one of its three case-integers (invisibility trichotomy, RESULTS-CHAR0-RIGOR).
One prime is therefore strong evidence, NOT proof; rigor at n = 128 needs a clean
ladder of k(128) = 2*cap(3^96) + cap(54^64) + 1 split primes (computed exactly below).

Usage:
  probe_reciprocal_census.py gate          # n=32 + n=64 reproduction gates
  probe_reciprocal_census.py run 128       # main run, smallest split prime
  probe_reciprocal_census.py run 128 --second  # second split prime
  probe_reciprocal_census.py verify6 8 16 32 64 128
      # multi-prime EXACT certificates for every count-5/count-6 plane:
      # for the cross-product normal v of a surface triple, |sigma(v_k)| <= 3*sqrt(3)
      # (RESULTS-CHAR0-RIGOR 1c), so xi = v.P(i,j) has |sigma(xi)| <= 12*sqrt(3) and
      # N(xi)^2 <= 432^m; if xi vanishes at k distinct split primes with
      # (prod p_i)^2 > 432^m then xi = 0 EXACTLY (norm/divisibility lemma).  The
      # intersection of the mod-p_i incidence sets over such a prime ladder is the
      # EXACT char-0 incidence set of the exact plane spanned by the chosen triple.
Outputs: results_reciprocal_census.json, results_count56_verify.json.
"""

import gzip
import json
import math
import os
import shutil
import subprocess
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "results_reciprocal_census.json")
TMPDIR = os.path.join(HERE, "tmp_recip_census")

WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
NWORK = 6

KNOWN_HISTOGRAMS = {   # original census engine, same smallest split prime
    (32, 268435649): {3: 326472, 4: 28056, 5: 260, 6: 1932},
    (64, 268435649): {3: 6778728, 4: 249368, 5: 580, 6: 9420},
}


def is_prime(m):
    if m < 2:
        return False
    for q in WITNESSES:
        if m % q == 0:
            return m == q
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in WITNESSES:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def split_primes(n, count, lower=1 << 28):
    p = lower + 1
    p += (-(p - 1)) % n
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def order_n_element(p, n):
    fs = set()
    mm, d = p - 1, 2
    while d * d <= mm:
        while mm % d == 0:
            fs.add(d)
            mm //= d
        d += 1
    if mm > 1:
        fs.add(mm)
    g = 2
    while not all(pow(g, (p - 1) // f, p) != 1 for f in fs):
        g += 1
    z = pow(g, (p - 1) // n, p)
    assert pow(z, n, p) == 1 and pow(z, n // 2, p) == p - 1
    return z


# ------------------------------------------------------------------ shared point setup

def build_points(n, p, z):
    zp = [pow(z, k, p) for k in range(n)]
    pts = []
    for i in range(n):
        zi = zp[i]
        for j in range(n):
            pts.append((zp[(i + j) % n], zp[j], zi))     # 4th coord 1 implicit
    assert pts[0] == (1, 1, 1)
    assert len(set(pts)) == n * n, "surface points must be distinct mod p"
    diffs = []
    for (x, y, u) in pts:
        diffs.append(((y - x) % p, (u - x) % p, (1 - x) % p,
                      (u - y) % p, (1 - y) % p))
    return pts, diffs


# ------------------------------------------------------------------ pass 1 worker

_G = {}


def _init_pass1(n, p, z, tag):
    _G.update(n=n, p=p, z=z, tag=tag)
    _G["pts"], _G["diffs"] = build_points(n, p, z)


def _pass1_worker(w):
    n, p = _G["n"], _G["p"]
    diffs = _G["diffs"]
    N = n * n
    pm2 = p - 2
    path = os.path.join(TMPDIR, f"{_G['tag']}_w{w}.gz")
    fh = gzip.open(path, "wt", compresslevel=1)
    buf = []
    n_rank2 = n_norm = n_sing = n_pairs = 0
    for qi in range(1 + w, N - 1, NWORK):
        aq, bq, cq, dq, eq = diffs[qi]
        for ar, br, cr, dr, er in diffs[qi + 1:]:
            n_pairs += 1
            v0 = (dq * er - eq * dr) % p
            v1 = (cq * br - bq * cr) % p
            v2 = (aq * cr - cq * ar) % p
            v3 = (bq * ar - aq * br) % p
            if v0 == 0:
                if v1 == 0 and v2 == 0 and v3 == 0:
                    n_rank2 += 1
                    continue
                if v3 == 0:
                    n_norm += 1
                    continue
                if (v1 * v2) % p == 0:
                    n_sing += 1
                    continue
            else:
                if v1 == 0 and v2 == 0:
                    n_norm += 1
                    continue
                if (v0 * v3 - v1 * v2) % p == 0:
                    n_sing += 1
                    continue
            if v0:
                if v0 != 1:
                    inv = pow(v0, pm2, p)
                    v1 = v1 * inv % p
                    v2 = v2 * inv % p
                    v3 = v3 * inv % p
                    v0 = 1
            elif v1:
                if v1 != 1:
                    inv = pow(v1, pm2, p)
                    v2 = v2 * inv % p
                    v3 = v3 * inv % p
                    v1 = 1
            elif v2 != 1:
                inv = pow(v2, pm2, p)
                v3 = v3 * inv % p
                v2 = 1
            key = ((v0 << 31 | v1) << 31 | v2) << 31 | v3
            buf.append(f"{key:031x}\n")
            if len(buf) >= 200_000:
                fh.write("".join(buf))
                buf.clear()
    fh.write("".join(buf))
    fh.close()
    return n_rank2, n_norm, n_sing, n_pairs, path


# ------------------------------------------------------------------ in-loop identity spot check

def reciprocity_identity_spotcheck(n, p, z, samples=2000, seed=375):
    """rev(cross(P00,Q,R)) == z^Sigma * cross(P00, conjQ, conjR) mod p, where
    conj P(i,j) = P(-i,-j) (the mod-p shadow of the exact spanning identity)."""
    import random
    rng = random.Random(seed)
    zp = [pow(z, k, p) for k in range(n)]

    def P(i, j):
        return (zp[(i + j) % n], zp[j % n], zp[i % n], 1)

    def cross(A, B, C):
        out = []
        s = 1
        M = [A, B, C]
        for k in range(4):
            sub = [[M[r][c] for c in range(4) if c != k] for r in range(3)]
            det = (sub[0][0] * (sub[1][1] * sub[2][2] - sub[1][2] * sub[2][1])
                   - sub[0][1] * (sub[1][0] * sub[2][2] - sub[1][2] * sub[2][0])
                   + sub[0][2] * (sub[1][0] * sub[2][1] - sub[1][1] * sub[2][0])) % p
            out.append(s * det % p)
            s = -s
        return out

    bad = 0
    for _ in range(samples):
        i1, j1, i2, j2 = (rng.randrange(n) for _ in range(4))
        if (i1, j1) in ((0, 0), (i2, j2)) or (i2, j2) == (0, 0):
            continue
        v = cross(P(0, 0), P(i1, j1), P(i2, j2))
        w = cross(P(0, 0), P(-i1, -j1), P(-i2, -j2))
        S = (i1 + j1 + i2 + j2) % n
        zS = zp[S]
        if [v[3], v[2], v[1], v[0]] != [zS * wk % p for wk in w]:
            bad += 1
    return bad


# ------------------------------------------------------------------ flats (as in census)

def flats_check(n, p, pts, diffs):
    N = n * n
    dir_buckets = {}
    for idx in range(1, N):
        a, b, c = diffs[idx][0], diffs[idx][1], diffs[idx][2]
        if a:
            inv = pow(a, p - 2, p)
            key = (1, b * inv % p, c * inv % p)
        elif b:
            inv = pow(b, p - 2, p)
            key = (0, 1, c * inv % p)
        else:
            key = (0, 0, 1)
        dir_buckets.setdefault(key, []).append(idx)
    flats = []
    expected_rank2 = 0
    for key, idxs in dir_buckets.items():
        if len(idxs) >= 2:
            L = len(idxs) + 1
            expected_rank2 += (L - 1) * (L - 2) // 2
            ijs = sorted([(0, 0)] + [divmod(ix, n) for ix in idxs])
            is_i0 = all(i == 0 for (i, j) in ijs)
            is_j0 = all(j == 0 for (i, j) in ijs)
            flats.append({"L": L, "is_coordinate_line": bool(is_i0 or is_j0)})
    coord_lines_only = (len(flats) == 2 and all(f["is_coordinate_line"] for f in flats)
                        and all(f["L"] == n for f in flats))
    return flats, expected_rank2, coord_lines_only


# ------------------------------------------------------------------ recount workers

def _init_recount(n, p, z):
    _G.update(n=n, p=p, z=z)
    zp = [pow(z, k, p) for k in range(n)]
    _G["zp"] = zp
    _G["powset"] = set(zp)


def _recount_worker(chunk):
    """chunk: list of (key, mult).  Returns list of (key, mult, count)."""
    n, p = _G["n"], _G["p"]
    zp, powset = _G["zp"], _G["powset"]
    M31 = (1 << 31) - 1
    out = []
    for key, mult in chunk:
        v3 = key & M31
        v2 = (key >> 31) & M31
        v1 = (key >> 62) & M31
        v0 = key >> 93
        dens = []
        nums = []
        for zi in zp:
            dens.append((v0 * zi + v1) % p)
            nums.append((-(v2 * zi + v3)) % p)
        # batched inversion of nonzero dens
        idx = [i for i, d in enumerate(dens) if d]
        for i in range(n):
            if not dens[i]:
                assert nums[i], "den==0 with num==0: singular plane in recount"
        pref = []
        acc = 1
        for i in idx:
            acc = acc * dens[i] % p
            pref.append(acc)
        inv_acc = pow(acc, p - 2, p)
        c = 0
        for t in range(len(idx) - 1, -1, -1):
            i = idx[t]
            inv_d = inv_acc * (pref[t - 1] if t else 1) % p
            inv_acc = inv_acc * dens[i] % p
            if nums[i] * inv_d % p in powset:
                c += 1
        out.append((key, mult, c))
    return out


def brute_count(key, n, p, zp):
    M31 = (1 << 31) - 1
    v3 = key & M31
    v2 = (key >> 31) & M31
    v1 = (key >> 62) & M31
    v0 = key >> 93
    c = 0
    for i in range(n):
        for j in range(n):
            if (v0 * zp[(i + j) % n] + v1 * zp[j] + v2 * zp[i] + v3) % p == 0:
                c += 1
    return c


def incidence_set(key, n, p, zp):
    M31 = (1 << 31) - 1
    v3 = key & M31
    v2 = (key >> 31) & M31
    v1 = (key >> 62) & M31
    v0 = key >> 93
    out = []
    for i in range(n):
        for j in range(n):
            if (v0 * zp[(i + j) % n] + v1 * zp[j] + v2 * zp[i] + v3) % p == 0:
                out.append((i, j))
    return out


def canon_translate(ij_set, n):
    best = None
    for (s, t) in ij_set:
        cand = tuple(sorted(((i - s) % n, (j - t) % n) for (i, j) in ij_set))
        if best is None or cand < best:
            best = cand
    return best


# ------------------------------------------------------------------ exact 5/6 certificates

def moebius_set(key, n, p, zp, dlog):
    """Mod-p incidence set of plane `key`, O(n): z^j = -(v2 z^i + v3)/(v0 z^i + v1)."""
    M31 = (1 << 31) - 1
    v3 = key & M31
    v2 = (key >> 31) & M31
    v1 = (key >> 62) & M31
    v0 = key >> 93
    dens, nums = [], []
    for zi in zp:
        dens.append((v0 * zi + v1) % p)
        nums.append((-(v2 * zi + v3)) % p)
    idx = [i for i, d in enumerate(dens) if d]
    for i in range(n):
        if not dens[i]:
            assert nums[i], "den==0 with num==0: singular plane"
    pref = []
    acc = 1
    for i in idx:
        acc = acc * dens[i] % p
        pref.append(acc)
    inv_acc = pow(acc, p - 2, p)
    out = set()
    for t in range(len(idx) - 1, -1, -1):
        i = idx[t]
        inv_d = inv_acc * (pref[t - 1] if t else 1) % p
        inv_acc = inv_acc * dens[i] % p
        r = nums[i] * inv_d % p
        j = dlog.get(r)
        if j is not None:
            out.add((i, j))
    return out


def cross_from_triple(trip, zp, p, n):
    """Cross product of (P(i0,j0), P(i1,j1), P(i2,j2)) reduced at p (exact formula
    commutes with reduction)."""
    rows = [(zp[(i + j) % n], zp[j % n], zp[i % n], 1) for (i, j) in trip]
    out = []
    s = 1
    for k in range(4):
        sub = [[rows[r][c] for c in range(4) if c != k] for r in range(3)]
        det = (sub[0][0] * (sub[1][1] * sub[2][2] - sub[1][2] * sub[2][1])
               - sub[0][1] * (sub[1][0] * sub[2][2] - sub[1][2] * sub[2][0])
               + sub[0][2] * (sub[1][0] * sub[2][1] - sub[1][1] * sub[2][0])) % p
        out.append(s * det % p)
        s = -s
    return out


def pack_key(v, p):
    nz = next(i for i in range(4) if v[i])
    inv = pow(v[nz], p - 2, p)
    w = [x * inv % p for x in v]
    return ((w[0] << 31 | w[1]) << 31 | w[2]) << 31 | w[3]


def _init_cert(n, primes):
    _G.update(n=n, primes=primes, tabs={})
    for p in primes:
        z = order_n_element(p, n)
        zp = [pow(z, k, p) for k in range(n)]
        _G["tabs"][p] = (zp, {v: k for k, v in enumerate(zp)})


def _cert_worker(chunk):
    """chunk: list of (sorted incidence point tuples).  For each plane, fix ONE char-0
    rank-3 triple (through (0,0)), reduce its exact cross at every ladder prime, and
    intersect the mod-p incidence sets => the EXACT incidence set (height + norm lemma).
    Returns (n_ok_count, failures)."""
    n, primes = _G["n"], _G["primes"]
    ok, fails = 0, []
    for pts in chunk:
        assert pts[0] == (0, 0), "plane must pass through P(0,0)"
        p0 = primes[0]
        zp0, _ = _G["tabs"][p0]
        trip = None
        for a in range(1, len(pts)):
            for b in range(a + 1, len(pts)):
                cand = ((0, 0), pts[a], pts[b])
                if any(cross_from_triple(cand, zp0, p0, n)):
                    trip = cand
                    break
            if trip:
                break
        if trip is None:
            fails.append({"pts": [list(q) for q in pts], "why": "no rank-3 triple at p0"})
            continue
        inter = None
        degenerate = 0
        for p in primes:
            zp, dlog = _G["tabs"][p]
            v = cross_from_triple(trip, zp, p, n)
            if not any(v):
                degenerate += 1     # contributes incidence set = everything
                continue
            s = moebius_set(pack_key(v, p), n, p, zp, dlog)
            inter = s if inter is None else (inter & s)
        if degenerate or inter is None or sorted(inter) != list(pts):
            fails.append({"pts": [list(q) for q in pts], "why": "exact set mismatch",
                          "exact_set": sorted(map(list, inter or [])),
                          "degenerate_primes": degenerate})
        else:
            ok += 1
    return ok, fails


def verify_count56(n):
    """Pipeline at the smallest split prime + exact certificates for every count-5/6
    plane.  Proves char-0 tallies count6(n) >= observed, count5(n) >= observed."""
    # exact ladder length: (prod p)^2 > 432^m with all p > 2^28
    m = n // 2
    need = 1
    while (1 << (2 * 28 * need)) <= 432 ** m:
        need += 1
    k = need + 1                                   # +1 margin
    primes = split_primes(n, k)
    prodsq = 1
    for p in primes:
        prodsq *= p * p
    assert prodsq > 432 ** m and len(set(primes)) == k
    print(f"== verify56 n={n}: ladder of {k} split primes (need {need}: "
          f"(prod p)^2 > 432^{m}); pipeline at p1={primes[0]}", flush=True)
    res = run_census(n, primes[0], keep_sets=(5, 6))
    sets56 = res.pop("_sets56")
    by_count = {5: [], 6: []}
    for c, pts in sets56:
        by_count[c].append(tuple(map(tuple, pts)))
    out = {"n": n, "primes": primes, "k_ladder": k,
           "norm_bound_bits": (432 ** m).bit_length()}
    with Pool(NWORK, initializer=_init_cert, initargs=(n, primes)) as pool:
        for c in (5, 6):
            planes = by_count[c]
            chunks = [planes[i::NWORK] for i in range(NWORK)]
            got = pool.map(_cert_worker, chunks)
            n_ok = sum(g[0] for g in got)
            fails = [f for g in got for f in g[1]]
            out[f"count{c}_modp"] = len(planes)
            out[f"count{c}_char0_proven"] = n_ok
            out[f"count{c}_failures"] = fails
            print(f"   count-{c}: {len(planes)} mod-p planes -> {n_ok} PROVEN char-0 "
                  f"(failures: {len(fails)})", flush=True)
    return out


# ------------------------------------------------------------------ ladder length k(n)

def ladder_k(n):
    m = n // 2
    B_coord = 3 ** (3 * m // 2)
    B_det = 54 ** m

    def cap(B):
        t = 0
        while (1 << (28 * (t + 1))) < B:
            t += 1
        return t

    return {"m": m, "cap_coord": cap(B_coord), "cap_det": cap(B_det),
            "k_needed": 2 * cap(B_coord) + cap(B_det) + 1}


# ------------------------------------------------------------------ main census

def run_census(n, p, keep_sets=None):
    t_all = time.time()
    z = order_n_element(p, n)
    N = n * n
    print(f"== n={n} p={p} z={z}: reciprocal-family census "
          f"(reciprocity automatic for spanned planes)", flush=True)
    os.makedirs(TMPDIR, exist_ok=True)

    bad_ident = reciprocity_identity_spotcheck(n, p, z)
    assert bad_ident == 0, f"mod-p spanning-identity spot check FAILED ({bad_ident})"
    print(f"   spanning identity rev(v) = z^Sigma*conj(v) mod p: 0 failures "
          f"(~2000 samples)", flush=True)

    pts, diffs = build_points(n, p, z)
    flats, expected_rank2, coord_lines_only = flats_check(n, p, pts, diffs)
    assert coord_lines_only, f"unexpected flats: {flats}"

    # ---- pass 1 (6 workers, streamed to gzip)
    t0 = time.time()
    tag = f"n{n}_p{p}"
    with Pool(NWORK, initializer=_init_pass1, initargs=(n, p, z, tag)) as pool:
        results = pool.map(_pass1_worker, range(NWORK))
    n_rank2 = sum(r[0] for r in results)
    n_norm = sum(r[1] for r in results)
    n_sing = sum(r[2] for r in results)
    n_pairs = sum(r[3] for r in results)
    paths = [r[4] for r in results]
    t_pass1 = time.time() - t0
    assert n_pairs == (N - 1) * (N - 2) // 2, "pair enumeration incomplete"
    assert n_rank2 == expected_rank2, \
        f"rank-2 triples {n_rank2} != bucket prediction {expected_rank2}"
    sz = sum(os.path.getsize(pp) for pp in paths)
    print(f"   pass1: {n_pairs} pairs in {t_pass1:.0f}s; rank2 {n_rank2} (= predicted), "
          f"normalizer {n_norm}, singular {n_sing}; gz {sz/1e9:.2f} GB", flush=True)

    # ---- dedupe via external sort (disk, compressed temps)
    t0 = time.time()
    cands_path = os.path.join(TMPDIR, f"{tag}_cands.txt")
    cmd = (f"zcat {' '.join(paths)} | LC_ALL=C sort -S 1500M --parallel={NWORK} "
           f"-T {TMPDIR} --compress-program=gzip | uniq -c | "
           f"awk '{{n++; if ($1 > 1) print $1, $2}} END {{print \"TOTAL\", n}}' "
           f"> {cands_path}")
    subprocess.run(["bash", "-c", cmd], check=True)
    cands = []
    total_distinct = None
    with open(cands_path) as fh:
        for line in fh:
            a, b = line.split()
            if a == "TOTAL":
                total_distinct = int(b)
            else:
                cands.append((int(b, 16), int(a)))
    assert total_distinct is not None
    t_sort = time.time() - t0
    for pp in paths:
        os.remove(pp)
    print(f"   dedupe: {total_distinct} distinct planes, {len(cands)} with mult>=2 "
          f"({t_sort:.0f}s)", flush=True)

    # ---- recount (6 workers, Moebius O(n) per plane)
    t0 = time.time()
    chunks = [cands[i::NWORK] for i in range(NWORK)]
    with Pool(NWORK, initializer=_init_recount, initargs=(n, p, z)) as pool:
        rec = [r for sub in pool.map(_recount_worker, chunks) for r in sub]
    t_rec = time.time() - t0

    zp = [pow(z, k, p) for k in range(n)]
    # in-run validation of the fast counter against the brute O(n^2) counter
    for key, mult, c in rec[:200]:
        assert brute_count(key, n, p, zp) == c, "fast Moebius counter mismatch"

    sets56 = None
    if keep_sets:
        dlog = {v: k for k, v in enumerate(zp)}
        sets56 = []
        for key, mult, c in rec:
            if c in keep_sets:
                s = moebius_set(key, n, p, zp, dlog)
                assert len(s) == c and (0, 0) in s
                sets56.append((c, sorted(s)))

    hist = {3: total_distinct - len(cands)}
    for key, mult, c in rec:
        assert c >= 4, f"mult>=2 plane recounted below 4 (lemma violation): {key:x}"
        hist[c] = hist.get(c, 0) + 1
    max_count = max(hist)
    over6 = [(f"{key:031x}", mult, c) for key, mult, c in rec if c > 6]
    top = sorted((r for r in rec if r[2] == max_count), key=lambda r: r[0])[:3]
    top_sets = []
    for key, mult, c in top:
        ij = incidence_set(key, n, p, zp)
        assert len(ij) == c
        top_sets.append({"key_hex": f"{key:031x}", "count": c,
                         "canon_ij": [list(q) for q in canon_translate(ij, n)]})
    Sn = sorted([(0, 0), (1, 1), (2, 3), (4, n // 2 + 2),
                 (n // 2 - 1, n - 3), (n - 2, n - 1)])
    res = {
        "n": n, "p": p, "z": z,
        "n_pairs": n_pairs, "n_rank2": n_rank2, "n_normalizer_skipped": n_norm,
        "n_singular_skipped": n_sing, "n_distinct_planes": total_distinct,
        "n_mult_ge2": len(cands),
        "histogram": {str(k): v for k, v in sorted(hist.items())},
        "M_p": max_count,
        "count6_planes": hist.get(6, 0),
        "planes_over_6": over6,
        "flats_coordinate_lines_only": coord_lines_only,
        "top_max_planes": top_sets,
        "top1_canon_is_Sn": (top_sets and
                             top_sets[0]["canon_ij"] == [list(q) for q in Sn]),
        "identity_spotcheck_failures": bad_ident,
        "timing_sec": {"pass1": round(t_pass1, 1), "sort": round(t_sort, 1),
                       "recount": round(t_rec, 1),
                       "total": round(time.time() - t_all, 1)},
    }
    if sets56 is not None:
        res["_sets56"] = sets56
    print(f"   histogram {res['histogram']}  M_p={max_count}  count6={res['count6_planes']}"
          f"  over6={len(over6)}  total {res['timing_sec']['total']}s", flush=True)
    os.remove(cands_path)
    return res


def merge_save(res):
    data = {}
    if os.path.exists(OUT_JSON):
        try:
            with open(OUT_JSON) as fh:
                data = json.load(fh)
        except Exception:
            data = {}
    data.setdefault("runs", {})
    data["runs"][f"n{res['n']}_p{res['p']}"] = res
    data["ladder_k"] = {str(n): ladder_k(n) for n in (32, 64, 128, 256)}
    with open(OUT_JSON, "w") as fh:
        json.dump(data, fh, indent=1)


def main():
    args = sys.argv[1:]
    mode = args[0] if args else "gate"
    if mode == "gate":
        for n in (32, 64):
            p = split_primes(n, 1)[0]
            res = run_census(n, p)
            known = KNOWN_HISTOGRAMS.get((n, p))
            got = {int(k): v for k, v in res["histogram"].items()}
            assert known is not None and got == known, \
                f"GATE FAILED n={n} p={p}: got {got}, expected {known}"
            print(f"   GATE n={n} p={p}: histogram reproduces original census exactly",
                  flush=True)
            merge_save(res)
    elif mode == "run":
        n = int(args[1])
        idx = 1 if "--second" in args else 0
        p = split_primes(n, idx + 1)[idx]
        res = run_census(n, p)
        merge_save(res)
    elif mode == "verify6":
        path = os.path.join(HERE, "results_count56_verify.json")
        data = {}
        if os.path.exists(path):
            try:
                with open(path) as fh:
                    data = json.load(fh)
            except Exception:
                data = {}
        for a in args[1:]:
            out = verify_count56(int(a))
            data[str(out["n"])] = out
            with open(path, "w") as fh:
                json.dump(data, fh, indent=1)
        print(json.dumps({k: {"count6": v["count6_char0_proven"],
                              "count5": v["count5_char0_proven"]}
                          for k, v in data.items()}, indent=0))
    else:
        raise SystemExit(f"unknown mode {mode}")
    shutil.rmtree(TMPDIR, ignore_errors=True)
    print("done.", flush=True)


if __name__ == "__main__":
    main()

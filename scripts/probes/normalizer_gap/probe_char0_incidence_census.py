#!/usr/bin/env python3
"""
probe_char0_incidence_census.py -- ArkLib#371 normalizer-gap lane (claim 4687191139).

Char-0 incidence census: M(n) = max, over hyperplanes h in K^4 (K = Q(zeta_n)) that are
NOT of normalizer type (b=c=0 or a=d=0) and have invertible matrix (ad != bc), of
#{(i,j) in (Z/n)^2 : P(i,j) on h}, where P(i,j) = (z^{i+j}, z^j, z^i, 1) and the
hyperplane normal is read as (c, d, -a, -b) against these coordinates
(incidence (zeta^i, zeta^j) for sigma=[[a,b],[c,d]]: c z^{i+j} + d z^j - a z^i - b = 0).

Method: reduce mod TWO split primes p == 1 (mod n), p > 2^28 (smallest such).
In F_p take z of exact order n; enumerate candidate hyperplanes as spans of point
triples with the first point fixed to P(0,0) = (1,1,1,1) (torus-action quotient:
(i,j) -> (i+s, j+t) conjugates sigma in PGL2, preserves non-normalizer-ness and the
incidence count, so every orbit of incidence sets has a representative through (0,0)).

For each triple (P00, Q, R): the rank-3 nullspace normal is the generalized cross
product v_k = (-1)^k det(3x3 minor dropping column k).  v == 0 <=> rank 2 (collinear
triple -> degenerate flat, handled separately by direction-bucketing).  Skip normalizer
type (v0==v3==0 i.e. b=c=0, or v1==v2==0 i.e. a=d=0; from (c,d,-a,-b)=(v0,v1,v2,v3):
a=-v2, b=-v3, c=v0, d=v1) and singular (ad-bc = v0*v3 - v1*v2 == 0 mod p).  Dedupe by
normalized normal (first nonzero scaled to 1), dict normal -> triple-multiplicity m.

Key fact (proved in comments below): a deduped rank-3 plane has m == 1  <=>  its full
incidence count c == 3.  So exact recounting over all n^2 points is only needed for
keys with m >= 2; the m==1 keys are exactly the count-3 bucket of the histogram.

Degenerate flats: rank-2 point sets through P00 = lines {R : R - r0*P00 || Q - q0*P00};
found by bucketing all points by normalized direction (d1,d2,d3) = (P1-P0, P2-P0, P3-P0)
(sic: coords (z^{i+j}, z^j, z^i, 1) minus P0 * (1,1,1,1) has 0 in slot 0 -- direction
taken in the remaining 3 slots after subtracting P0 from each).  A flat with L points
lies on a pencil of p+1 hyperplanes; it contributes an achievable incidence count L iff
the pencil is not identically singular / identically normalizer-type (checked exactly:
the singular form is a quadratic on the pencil -- identically zero iff 3 coefficient
conditions; normalizer patterns are linear -- identically satisfied iff 4 coords vanish).

Exact integer arithmetic throughout (mod p); deterministic Miller-Rabin (64-bit exact
with witnesses {2,...,37}).

Usage: probe_char0_incidence_census.py [n ...]     (default: 8 16 32 64)
Merges results into results_char0_census.json and regenerates RESULTS-CHAR0.md.
"""

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(HERE, "results_char0_census.json")
MD_PATH = os.path.join(HERE, "RESULTS-CHAR0.md")

WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


# ---------------------------------------------------------------- primality / field setup

def is_prime(m: int) -> bool:
    """Deterministic Miller-Rabin, exact for m < 3.3e24 with this witness set."""
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
        if x == 1 or x == m - 1:
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def split_primes(n: int, count: int = 2, lower: int = 1 << 28):
    """Smallest `count` primes p == 1 (mod n) with p > lower."""
    p = lower + 1
    p += (-(p - 1)) % n          # adjust to p == 1 (mod n), p > lower
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def factor(m: int):
    fs = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs[d] = fs.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        fs[m] = fs.get(m, 0) + 1
    return fs


def order_n_element(p: int, n: int) -> int:
    """z in F_p* of exact multiplicative order n (n a power of two here)."""
    fs = list(factor(p - 1))
    g = 2
    while not all(pow(g, (p - 1) // f, p) != 1 for f in fs):
        g += 1
    z = pow(g, (p - 1) // n, p)
    assert pow(z, n, p) == 1, "z^n != 1"
    assert n == 1 or pow(z, n // 2, p) != 1, "z has order < n"
    return z


# ---------------------------------------------------------------- small linear algebra (self-check)

def nullspace_rank3_bruteforce(rows, p):
    """Fraction-free Gaussian elimination of a 3x4 matrix mod p -> (rank, normal or None)."""
    m = [list(r) for r in rows]
    rank, piv_cols = 0, []
    for col in range(4):
        piv = None
        for r in range(rank, 3):
            if m[r][col] % p:
                piv = r
                break
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        inv = pow(m[rank][col], p - 2, p)
        m[rank] = [(x * inv) % p for x in m[rank]]
        for r in range(3):
            if r != rank and m[r][col] % p:
                f = m[r][col]
                m[r] = [(m[r][k] - f * m[rank][k]) % p for k in range(4)]
        piv_cols.append(col)
        rank += 1
        if rank == 3:
            break
    if rank < 3:
        return rank, None
    free = next(c for c in range(4) if c not in piv_cols)
    v = [0, 0, 0, 0]
    v[free] = 1
    for r, c in enumerate(piv_cols):
        v[c] = (-m[r][free]) % p
    return 3, tuple(v)


def cross_normal(P00, Q, R, p):
    """Generalized cross product of 3 rows of a 3x4 matrix (first row all ones)."""
    q0, q1, q2, q3 = Q
    r0, r1, r2, r3 = R
    aq, bq, cq = (q1 - q0) % p, (q2 - q0) % p, (q3 - q0) % p
    dq, eq = (q2 - q1) % p, (q3 - q1) % p
    ar, br, cr = (r1 - r0) % p, (r2 - r0) % p, (r3 - r0) % p
    dr, er = (r2 - r1) % p, (r3 - r1) % p
    v0 = (dq * er - eq * dr) % p
    v1 = (cq * br - bq * cr) % p
    v2 = (aq * cr - cq * ar) % p
    v3 = (bq * ar - aq * br) % p
    return (v0, v1, v2, v3)


def self_test():
    """Verify cross_normal against brute-force nullspace on random triples."""
    import random
    rng = random.Random(371)
    p = 268_435_459
    while not is_prime(p):
        p += 1
    P00 = (1, 1, 1, 1)
    for _ in range(500):
        Q = tuple(rng.randrange(p) for _ in range(4))
        R = tuple(rng.randrange(p) for _ in range(4))
        v = cross_normal(P00, Q, R, p)
        rank, w = nullspace_rank3_bruteforce([P00, Q, R], p)
        for row in (P00, Q, R):
            assert sum(a * b for a, b in zip(row, v)) % p == 0, "cross normal not in nullspace"
        if rank == 3:
            assert any(v), "cross normal zero on a rank-3 triple"
            # v and w must be proportional
            k = next(i for i in range(4) if w[i])
            lam = (v[k] * pow(w[k], p - 2, p)) % p
            assert all((lam * w[i] - v[i]) % p == 0 for i in range(4)), "normals disagree"
        else:
            assert not any(v), "nonzero cross normal on a rank<3 triple"


# ---------------------------------------------------------------- pencil validity for flats

def nullspace2_basis(Q, p):
    """Basis (u, w) of the 2-dim space of normals vanishing on P00=(1,1,1,1) and Q."""
    q0, q1, q2, q3 = Q
    d = ((q1 - q0) % p, (q2 - q0) % p, (q3 - q0) % p)   # row-reduced second row (0, d1, d2, d3)
    # constraints: x0+x1+x2+x3 == 0  and  d1*x1 + d2*x2 + d3*x3 == 0
    k = next(i for i in range(3) if d[i])               # pivot among x1..x3
    inv = pow(d[k], p - 2, p)
    basis = []
    free_idxs = [i for i in range(3) if i != k]
    for fi in free_idxs:
        x = [0, 0, 0, 0]
        x[1 + fi] = 1
        x[1 + k] = (-d[fi] * inv) % p
        x[0] = (-(x[1] + x[2] + x[3])) % p
        basis.append(tuple(x))
    return basis


def pencil_has_valid_member(Q, p):
    """For the flat span(P00, Q): does its hyperplane pencil contain a member that is
    invertible (ad != bc) and not normalizer-type?  Exact check (no sampling):
    - singular form S(v) = v0*v3 - v1*v2 restricted to the pencil {a*u + b*w} is a
      quadratic in (a,b); identically zero iff its 3 coefficients vanish mod p;
    - normalizer pattern v0==v3==0 (resp. v1==v2==0) holds identically iff
      u0==w0==u3==w3==0 (resp. u1==w1==u2==w2==0).
    If none holds identically, invalid members number <= 2 + 1 + 1 << p+1, and since
    off-flat points (< n^2 of them) each kill exactly one member, a valid member with
    incidence set exactly the flat exists."""
    u, w = nullspace2_basis(Q, p)
    c_aa = (u[0] * u[3] - u[1] * u[2]) % p
    c_bb = (w[0] * w[3] - w[1] * w[2]) % p
    c_ab = (u[0] * w[3] + u[3] * w[0] - u[1] * w[2] - u[2] * w[1]) % p
    sing_identical = (c_aa == 0 and c_bb == 0 and c_ab == 0)
    norm1_identical = (u[0] == 0 and w[0] == 0 and u[3] == 0 and w[3] == 0)
    norm2_identical = (u[1] == 0 and w[1] == 0 and u[2] == 0 and w[2] == 0)
    return not (sing_identical or norm1_identical or norm2_identical)


# ---------------------------------------------------------------- census core

def canon_translate(ij_set, n):
    """Canonical representative of an incidence set under the torus (i,j)->(i+s,j+t)."""
    best = None
    for (s, t) in ij_set:
        cand = tuple(sorted(((i - s) % n, (j - t) % n) for (i, j) in ij_set))
        if best is None or cand < best:
            best = cand
    return best


def census(n: int, p: int, recount_cap: int = 2_000_000, progress: bool = True):
    """Full incidence census mod p.  Returns a result dict."""
    t_start = time.time()
    z = order_n_element(p, n)
    N = n * n
    zp = [pow(z, k, p) for k in range(n)]
    # points P(i,j) = (z^{i+j}, z^j, z^i, 1); index i*n + j; P(0,0) at index 0
    pts = []
    for i in range(n):
        zi = zp[i]
        for j in range(n):
            pts.append((zp[(i + j) % n], zp[j], zi))   # 4th coord 1 implicit
    assert pts[0] == (1, 1, 1), "P(0,0) must be (1,1,1,1)"
    assert len(set(pts)) == N, "surface points must be distinct"

    # per-point difference precomputation for the cross product
    diffs = []
    for (x, y, u) in pts:
        diffs.append(((y - x) % p, (u - x) % p, (1 - x) % p,
                      (u - y) % p, (1 - y) % p))

    # ---- degenerate flats through P00: bucket points 1..N-1 by direction (a,b,c) normalized
    dir_buckets = {}
    for idx in range(1, N):
        a, b, c = diffs[idx][0], diffs[idx][1], diffs[idx][2]
        # normalize first nonzero to 1 ((a,b,c) != 0 since points are distinct)
        if a:
            inv = pow(a, p - 2, p)
            key = (1, b * inv % p, c * inv % p)
        elif b:
            inv = pow(b, p - 2, p)
            key = (0, 1, c * inv % p)
        else:
            key = (0, 0, 1)
        dir_buckets.setdefault(key, []).append(idx)
    flats = []   # (L, valid, sample point index)
    expected_rank2_triples = 0
    for key, idxs in dir_buckets.items():
        if len(idxs) >= 2:
            L = len(idxs) + 1   # including P00
            expected_rank2_triples += (L - 1) * (L - 2) // 2
            valid = pencil_has_valid_member(pts[idxs[0]] + (1,), p)
            flats.append({"L": L,
                          "pencil_has_valid_member": valid,
                          "point_ijs": sorted([(0, 0)] + [divmod(ix, n) for ix in idxs])})
    flats.sort(key=lambda f: -f["L"])
    deg_flat_max_valid = max((f["L"] for f in flats if f["pencil_has_valid_member"]), default=None)

    # ---- pass 1: all triples (P00, Q, R), Q < R, cross-product normal, dedupe + multiplicity
    counts = {}
    n_rank2 = 0
    n_norm_skip = 0
    n_sing_skip = 0
    pm2 = p - 2
    t0 = time.time()
    last_report = t0
    total_pairs = (N - 1) * (N - 2) // 2
    done_pairs = 0
    for qi in range(1, N - 1):
        aq, bq, cq, dq, eq = diffs[qi]
        rest = diffs[qi + 1:]
        cget = counts.get
        for ar, br, cr, dr, er in rest:
            v0 = (dq * er - eq * dr) % p
            v1 = (cq * br - bq * cr) % p
            v2 = (aq * cr - cq * ar) % p
            v3 = (bq * ar - aq * br) % p
            if v0 == 0:
                if v1 == 0 and v2 == 0 and v3 == 0:
                    n_rank2 += 1
                    continue
                if v3 == 0:                      # b = c = 0 : scaling normalizer
                    n_norm_skip += 1
                    continue
                if (v1 * v2) % p == 0:           # singular: v0*v3 - v1*v2 == 0
                    n_sing_skip += 1
                    continue
            else:
                if v1 == 0 and v2 == 0:          # a = d = 0 : inversion normalizer
                    n_norm_skip += 1
                    continue
                if (v0 * v3 - v1 * v2) % p == 0:
                    n_sing_skip += 1
                    continue
            # normalize first nonzero coordinate to 1, pack to int key
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
            counts[key] = cget(key, 0) + 1
        done_pairs += N - 1 - qi
        now = time.time()
        if progress and now - last_report > 15:
            last_report = now
            rate = done_pairs / (now - t0)
            eta = (total_pairs - done_pairs) / rate if rate else float("inf")
            print(f"    [n={n} p={p}] pass1 {done_pairs}/{total_pairs} "
                  f"({100*done_pairs/total_pairs:.1f}%)  {rate/1e6:.2f}M pairs/s  "
                  f"ETA {eta/60:.1f} min  dict={len(counts)}", flush=True)
    t_pass1 = time.time() - t0
    assert n_rank2 == expected_rank2_triples, (
        f"rank-2 triple count {n_rank2} != direction-bucket prediction {expected_rank2_triples}")

    # ---- histogram: m == 1 <=> incidence count 3 (proof: a rank-3 plane through P00 with
    # c >= 4 points splits its non-P00 points into >= 2 direction classes (1 class => rank 2);
    # cross-class pairs give rank-3 triples of the SAME plane: >= 2 of them whenever c >= 4).
    mult1 = sum(1 for m in counts.values() if m == 1)
    cand = [(key, m) for key, m in counts.items() if m >= 2]
    cand.sort(key=lambda km: -km[1])
    n_candidates = len(cand)
    capped = n_candidates > recount_cap
    if capped:
        cand = cand[:recount_cap]

    M31 = (1 << 31) - 1
    hist = {3: mult1}
    t1 = time.time()
    plane_counts = []
    for key, m in cand:
        v3 = key & M31
        v2 = (key >> 31) & M31
        v1 = (key >> 62) & M31
        v0 = key >> 93
        c = 0
        for (x, y, u) in pts:
            if (v0 * x + v1 * y + v2 * u + v3) % p == 0:
                c += 1
        plane_counts.append((c, m, (v0, v1, v2, v3)))
        hist[c] = hist.get(c, 0) + 1
    t_recount = time.time() - t1
    plane_counts.sort(key=lambda t: -t[0])

    rank3_max = plane_counts[0][0] if plane_counts else 3
    M_p = rank3_max
    if deg_flat_max_valid is not None and deg_flat_max_valid > M_p:
        M_p = deg_flat_max_valid

    # ---- top-5 argmax planes with incidence sets
    top5 = []
    for c, m, v in plane_counts[:5]:
        v0, v1, v2, v3 = v
        ij = []
        for idx, (x, y, u) in enumerate(pts):
            if (v0 * x + v1 * y + v2 * u + v3) % p == 0:
                ij.append(divmod(idx, n))
        assert len(ij) == c
        assert len({i for i, _ in ij}) == c, "incidence set must be a partial injection in i"
        assert c <= n, "incidence count cannot exceed n (partial bijection)"
        # matrix (a,b,c,d) = (-v2, -v3, v0, v1) mod p
        top5.append({
            "normal_cdab": [v0, v1, v2, v3],
            "matrix_abcd": [(-v2) % p, (-v3) % p, v0, v1],
            "count": c,
            "triple_multiplicity": m,
            "incidence_ij": sorted(ij),
            "incidence_canon": list(map(list, canon_translate(ij, n))),
        })

    result = {
        "n": n, "p": p, "z": z,
        "n_points": N,
        "n_triples": total_pairs,
        "n_rank2_triples": n_rank2,
        "n_normalizer_skipped": n_norm_skip,
        "n_singular_skipped": n_sing_skip,
        "n_distinct_planes": len(counts),
        "n_candidates_recounted": len(cand),
        "recount_capped": capped,
        "histogram": {str(k): v for k, v in sorted(hist.items())},
        "rank3_max": rank3_max,
        "degenerate_flats": flats,
        "degenerate_flat_max_valid": deg_flat_max_valid,
        "M_p": M_p,
        "top5": top5,
        "timing_sec": {"pass1": round(t_pass1, 2),
                       "recount": round(t_recount, 2),
                       "total": round(time.time() - t_start, 2)},
    }
    return result


# ---------------------------------------------------------------- driver / reporting

def run_n(n: int):
    p1, p2 = split_primes(n, 2)
    print(f"== n={n}: split primes {p1}, {p2} (smallest == 1 mod {n} above 2^28)", flush=True)
    res = {}
    for p in (p1, p2):
        print(f"  -- census n={n} p={p} ...", flush=True)
        r = census(n, p)
        print(f"     M_p={r['M_p']} (rank3_max={r['rank3_max']}, "
              f"flats_valid_max={r['degenerate_flat_max_valid']}) "
              f"planes={r['n_distinct_planes']} cand={r['n_candidates_recounted']} "
              f"t={r['timing_sec']['total']}s", flush=True)
        res[str(p)] = r
    Ms = [res[str(p1)]["M_p"], res[str(p2)]["M_p"]]
    agree = Ms[0] == Ms[1]
    # structural cross-check: canonical top-1 incidence sets match across primes?
    c1 = res[str(p1)]["top5"][0]["incidence_canon"] if res[str(p1)]["top5"] else None
    c2 = res[str(p2)]["top5"][0]["incidence_canon"] if res[str(p2)]["top5"] else None
    out = {
        "n": n,
        "primes": [p1, p2],
        "M_per_prime": {str(p1): Ms[0], str(p2): Ms[1]},
        "maxima_agree": agree,
        "M_candidate": min(Ms) if agree else None,
        "flagged": not agree,
        "top1_canon_sets_match": (c1 == c2),
        "per_prime": res,
    }
    return out


def write_md(data):
    lines = ["# Char-0 incidence census — M(n) for the normalizer-gap lane (ArkLib#371)",
             "",
             "M(n) = max over non-normalizer (b=c=0 / a=d=0 excluded), invertible (ad != bc)",
             "hyperplanes h of #{(i,j) in (Z/n)^2 : (z^{i+j}, z^j, z^i, 1) on h}, computed by",
             "reduction mod two split primes p == 1 (mod n), p > 2^28 (smallest such), with the",
             "torus-action quotient (first triple point fixed to P(0,0)).  M_p(n) >= M(n);",
             "agreement of the two primes (and of the canonical argmax (i,j)-sets) is the",
             "char-0 signal.",
             ""]
    lines.append("| n | p1 | p2 | M_p1 | M_p2 | agree | M(n) cand | top-1 sets match | deg-flat max (valid) |")
    lines.append("|---|----|----|------|------|-------|-----------|------------------|----------------------|")
    for nkey in sorted(data["runs"], key=int):
        r = data["runs"][nkey]
        p1, p2 = r["primes"]
        f1 = r["per_prime"][str(p1)]["degenerate_flat_max_valid"]
        f2 = r["per_prime"][str(p2)]["degenerate_flat_max_valid"]
        lines.append(f"| {nkey} | {p1} | {p2} | {r['M_per_prime'][str(p1)]} | "
                     f"{r['M_per_prime'][str(p2)]} | {r['maxima_agree']} | "
                     f"{r['M_candidate']} | {r['top1_canon_sets_match']} | {f1} / {f2} |")
    lines.append("")
    for nkey in sorted(data["runs"], key=int):
        r = data["runs"][nkey]
        lines.append(f"## n = {nkey}")
        for pstr, pr in r["per_prime"].items():
            h = ", ".join(f"{k}:{v}" for k, v in sorted(pr["histogram"].items(), key=lambda kv: int(kv[0])))
            lines.append(f"- p = {pstr} (z = {pr['z']}): histogram over deduped non-normalizer "
                         f"planes through P(0,0): {{{h}}}; rank-2 triples {pr['n_rank2_triples']}; "
                         f"normalizer-type skipped {pr['n_normalizer_skipped']}, singular skipped "
                         f"{pr['n_singular_skipped']}; pass1 {pr['timing_sec']['pass1']}s, "
                         f"recount {pr['timing_sec']['recount']}s.")
            if pr["degenerate_flats"]:
                fl = "; ".join(f"L={f['L']} valid={f['pencil_has_valid_member']}"
                               for f in pr["degenerate_flats"][:6])
                lines.append(f"  - degenerate flats (rank-2 point sets through P00): {fl}"
                             + (" ..." if len(pr["degenerate_flats"]) > 6 else ""))
            if pr["top5"]:
                t = pr["top5"][0]
                lines.append(f"  - argmax: count {t['count']}, canonical (i,j)-set "
                             f"{t['incidence_canon']}")
        lines.append("")
    with open(MD_PATH, "w") as fh:
        fh.write("\n".join(lines) + "\n")


def main(argv):
    ns = [int(a) for a in argv[1:]] or [8, 16, 32, 64]
    print("self-test (cross product vs brute-force nullspace) ...", flush=True)
    self_test()
    print("self-test OK", flush=True)
    data = {"runs": {}}
    if os.path.exists(JSON_PATH):
        try:
            with open(JSON_PATH) as fh:
                data = json.load(fh)
        except Exception:
            pass
    data.setdefault("runs", {})
    for n in ns:
        out = run_n(n)
        if n == 8:
            for pstr, pr in out["per_prime"].items():
                assert pr["M_p"] >= 6, f"calibration FAILED: n=8 census max {pr['M_p']} < 6 at p={pstr}"
            print("  calibration n=8: M_p >= 6 OK", flush=True)
        data["runs"][str(n)] = out
        with open(JSON_PATH, "w") as fh:
            json.dump(data, fh, indent=1, default=str)
        write_md(data)
        print(f"== n={n} done: M_per_prime={out['M_per_prime']} agree={out['maxima_agree']} "
              f"M_candidate={out['M_candidate']}", flush=True)
    print("all done.", flush=True)


if __name__ == "__main__":
    main(sys.argv)

#!/usr/bin/env python3
"""probe_dim1_interior_ceiling.py — dim-1 (constant-code) MCA interior bad-gamma ceiling probe.

Pre-registered probe: constant code C in F_p^n (codewords (c,...,c)), agreement
threshold a = 3, word pair (u0,u1), gamma in F_p.

  bad(gamma) <=> exists S subset of {0..n-1}, |S| >= a, (u0 + gamma*u1) constant on S,
                 and NOT (u0 constant on S AND u1 constant on S).

The domain x_i = g^i (g of multiplicative order n, p = 1 mod n) is sanity-checked
but plays no role for the constant code (the mcaEvent never evaluates domain points).

Pre-registered claims:
  C1  level-set criterion equivalence:
        bad(gamma) <=> exists c: L_c = {i : u0(i)+gamma*u1(i) = c} has |L_c| >= a
                       and i |-> (u1(i), u0(i)) is NON-constant on L_c.
      Verified byte-exact on the bad-gamma SET via THREE independent checkers
      (all-subset enumeration / level-set criterion / subset-enumeration inside
      level sets) on >= 500 random pairs at p=17, n=8, a=3.  Expected mismatches: 0.
  C2  ceiling: for EVERY (u0,u1): #{gamma : bad(gamma)} <= (n^2-n)/4
      (= 14 at n=8, 60 at n=16).  Max-search: structured families + designed
      collinear configs + hill-climb (mutate one plane point, accept if #bad
      non-decreasing), 200+ restarts, p in {17,41,113} at n=8 and
      p in {17,97,113} at n=16 (a=3 throughout).  KKH26 ceiling counts for the
      pin: 24 (mu=3, n=8) and 112 (mu=4, n=16); need maxbad < ceiling STRICTLY.
  C3  sharpness families in the plane picture (point P_i = (u1(i), u0(i)) = (z_i,y_i);
      gamma bad <=> some line y + gamma*z = c carries weight >= 3 with >= 2 fibers):
      x doubled points + y singletons, 2x + y = n, GENERIC position =>
        #bad = C(x,2) + x*y
      (spike x=1: n-2; multi-spike x=n/2: C(n/2,2); n=8 max at x in {2,3}: 9).
      Genericity is CERTIFIED explicitly (dd/ds pairs have distinct z, all dd+ds
      slopes pairwise distinct, no 3 singletons collinear); on certified samples
      the formula must hold EXACTLY.  Designed collinear extras: +1 per
      fresh-direction collinear singleton triple (n=8 x=2 design => 10;
      n=16 x=5 + complete-quadrilateral singletons => 44).

Exit 0 iff all pre-registered checks pass.
"""

import itertools
import sys
import time
import random
from collections import Counter

START = time.time()
RNG = random.Random(232_113_357)

FAIL = 0
ROWS = []  # verdict table rows: (claim, expected, observed, ok_or_None)


def report(name, ok, detail=""):
    global FAIL
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        FAIL += 1


def row(claim, expected, observed, ok):
    ROWS.append((claim, expected, observed, ok))


def info(msg):
    print("       " + msg, flush=True)


def elapsed():
    return time.time() - START


# ------------------------------------------------------------------ arithmetic
def is_prime(m):
    if m < 2:
        return False
    d = 2
    while d * d <= m:
        if m % d == 0:
            return False
        d += 1
    return True


def order_n_gen(p, n):
    """An element of multiplicative order exactly n (n a power of 2 here)."""
    for g in range(2, p):
        if pow(g, n, p) == 1 and pow(g, n // 2, p) != 1:
            return g
    return None


def inv(a, p):
    return pow(a % p, p - 2, p)


def slope(P, Q, p):
    """Slope of line through plane points P=(z,y), Q in F_p^2; requires z's differ."""
    return (Q[1] - P[1]) * inv(Q[0] - P[0], p) % p


# ------------------------------------------------- C1: three independent checkers
def bad_by_subsets_all(u0, u1, gamma, p, a, subsets):
    """Direct from definition: enumerate ALL S with |S| >= a."""
    n = len(u0)
    w = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    for S in subsets:
        c = w[S[0]]
        ok = True
        for i in S[1:]:
            if w[i] != c:
                ok = False
                break
        if not ok:
            continue
        # NOT (u0 const on S AND u1 const on S)
        c0, c1 = u0[S[0]], u1[S[0]]
        both_const = True
        for i in S[1:]:
            if u0[i] != c0 or u1[i] != c1:
                both_const = False
                break
        if not both_const:
            return True
    return False


def level_sets(u0, u1, gamma, p):
    groups = {}
    for i in range(len(u0)):
        v = (u0[i] + gamma * u1[i]) % p
        groups.setdefault(v, []).append(i)
    return groups


def bad_by_levelset_criterion(u0, u1, gamma, p, a):
    """The Lean-side criterion: some level set with |L_c| >= a, pair map non-constant."""
    for idxs in level_sets(u0, u1, gamma, p).values():
        if len(idxs) >= a:
            f = (u1[idxs[0]], u0[idxs[0]])
            for i in idxs[1:]:
                if (u1[i], u0[i]) != f:
                    return True
    return False


def bad_by_subsets_within_levelsets(u0, u1, gamma, p, a):
    """Independent cross-validator: enumerate subsets of each level set."""
    for idxs in level_sets(u0, u1, gamma, p).values():
        if len(idxs) < a:
            continue
        for k in range(a, len(idxs) + 1):
            for S in itertools.combinations(idxs, k):
                f = (u1[S[0]], u0[S[0]])
                if any((u1[i], u0[i]) != f for i in S[1:]):
                    return True
    return False


def badset(checker, u0, u1, p, a, *extra):
    return frozenset(g for g in range(p) if checker(u0, u1, g, p, a, *extra))


def rand_word(p, n, rng):
    return [rng.randrange(p) for _ in range(n)]


def lowent_word(p, n, rng):
    """Low-entropy word: values from a tiny alphabet -> forces heavy level sets/fibers."""
    alpha = rng.randrange(2, 5)
    vals = [rng.randrange(p) for _ in range(alpha)]
    return [vals[rng.randrange(alpha)] for _ in range(n)]


def run_c1(p, n, a, npairs, rng):
    subsets = [S for k in range(a, n + 1) for S in itertools.combinations(range(n), k)]
    mism = 0
    example = None
    nonempty = 0
    for t in range(npairs):
        if t % 2 == 0:
            u0, u1 = rand_word(p, n, rng), rand_word(p, n, rng)
        else:  # stress collisions
            u0 = lowent_word(p, n, rng)
            u1 = lowent_word(p, n, rng) if rng.random() < 0.7 else rand_word(p, n, rng)
        A = badset(bad_by_subsets_all, u0, u1, p, a, subsets)
        B = badset(bad_by_levelset_criterion, u0, u1, p, a)
        C = badset(bad_by_subsets_within_levelsets, u0, u1, p, a)
        if A:
            nonempty += 1
        if not (A == B == C):
            mism += 1
            if example is None:
                example = (u0, u1, A, B, C)
    return mism, nonempty, example


# --------------------------------------------------- C2/C3: plane-multiset engine
def count_bad_points(pts, p, a):
    """#distinct gamma in F_p that are bad, for the plane multiset pts=[(z,y),...]."""
    zs = [q[0] for q in pts]
    ys = [q[1] for q in pts]
    n = len(pts)
    bad = 0
    for g in range(p):
        groups = {}
        for t in range(n):
            v = (ys[t] + g * zs[t]) % p
            e = groups.get(v)
            if e is None:
                groups[v] = [1, t, False]
            else:
                e[0] += 1
                if not e[2]:
                    s = e[1]
                    if zs[s] != zs[t] or ys[s] != ys[t]:
                        e[2] = True
                if e[0] >= a and e[2]:
                    bad += 1
                    break
        # inner break falls through to next gamma
    return bad


def distinct_points(p, m, rng):
    s = set()
    while len(s) < m:
        s.add((rng.randrange(p), rng.randrange(p)))
    return list(s)


def assemble_mix(base, x):
    pts = []
    for t in range(x):
        pts += [base[t], base[t]]
    pts += base[x:]
    return pts


def mix_config(p, n, x, rng):
    """x doubled points + (n - 2x) singletons, all base points distinct, random."""
    return assemble_mix(distinct_points(p, n - x, rng), x)


def is_generic_mix(base, x, p):
    """Certify generic position for the x-doubles + singletons family.

    (1) every double-double and double-singleton pair has distinct z,
    (2) all dd + ds slopes pairwise distinct,
    (3) no 3 singletons collinear (incl. the harmless all-same-z case, rejected
        conservatively).
    Under (1)-(3): #bad == C(x,2) + x*y exactly.
    """
    doubles = base[:x]
    singles = base[x:]
    slopes = []
    for i in range(x):
        for j in range(i + 1, x):
            if doubles[i][0] == doubles[j][0]:
                return False
            slopes.append(slope(doubles[i], doubles[j], p))
    for d in doubles:
        for s in singles:
            if d[0] == s[0]:
                return False
            slopes.append(slope(d, s, p))
    if len(set(slopes)) != len(slopes):
        return False
    y = len(singles)
    for i in range(y):
        for j in range(i + 1, y):
            A, B = singles[i], singles[j]
            dz1, dy1 = B[0] - A[0], B[1] - A[1]
            for k in range(j + 1, y):
                C = singles[k]
                if (dz1 * (C[1] - A[1]) - dy1 * (C[0] - A[0])) % p == 0:
                    return False
    return True


def certified_mix(p, n, x, rng, want, tries):
    """Rejection-sample `want` certified-generic mix configs (or fewer if tries cap)."""
    out = []
    for _ in range(tries):
        base = distinct_points(p, n - x, rng)
        if is_generic_mix(base, x, p):
            out.append(assemble_mix(base, x))
            if len(out) >= want:
                break
    return out


def design10_n8(p, rng):
    """n=8: 2 doubles + 4 singletons with s1,s2,s3 collinear => generically 10 bad."""
    for _ in range(2000):
        D1, D2, s1, s2, s4 = distinct_points(p, 5, rng)
        if s1[0] == s2[0]:
            continue
        m = slope(s1, s2, p)
        z3 = rng.randrange(p)
        if z3 in (s1[0], s2[0]):
            continue
        s3 = (z3, (s1[1] + m * (z3 - s1[0])) % p)
        pts = [D1, D1, D2, D2, s1, s2, s3, s4]
        if len(set(pts)) != 6:
            continue
        return pts
    return None


def design_quadrilateral_n16(p, rng):
    """n=16: 5 doubles + 6 singletons forming a complete quadrilateral
    (4 lines of 3 singletons, distinct directions) => generically
    C(5,2) + 5*6 + 4 = 44 bad."""
    for _ in range(4000):
        ms = rng.sample(range(p), 4)
        bs = [rng.randrange(p) for _ in range(4)]
        pts_s = []
        for i in range(4):
            for j in range(i + 1, 4):
                d = (ms[i] - ms[j]) % p
                xx = (bs[j] - bs[i]) * inv(d, p) % p
                yy = (ms[i] * xx + bs[i]) % p
                pts_s.append((xx, yy))
        if len(set(pts_s)) != 6:
            continue
        doubles = distinct_points(p, 5, rng)
        if set(doubles) & set(pts_s):
            continue
        pts = []
        for d_ in doubles:
            pts += [d_, d_]
        pts += pts_s
        return pts
    return None


def shape_of(pts):
    return sorted(Counter(pts).values(), reverse=True)


def fmt_cfg(pts):
    cnt = Counter(pts)
    items = sorted(cnt.items(), key=lambda kv: (-kv[1], kv[0]))
    return "fibers " + str(shape_of(pts)) + " pts " + \
        " ".join(f"{pt}x{m}" if m > 1 else f"{pt}" for pt, m in items)


# ------------------------------------------------------------------- hill climb
def mutate(pts, p, rng):
    n = len(pts)
    new = list(pts)
    i = rng.randrange(n)
    r = rng.random()
    if r < 0.35:
        j = rng.randrange(n)
        while j == i:
            j = rng.randrange(n)
        new[i] = new[j]  # grow a fiber (doubles are the engines)
    elif r < 0.70:
        # collinear snap: put point i on the line through two other positions
        j, k = rng.sample([t for t in range(n) if t != i], 2)
        (zj, yj), (zk, yk) = new[j], new[k]
        if zj == zk:
            new[i] = (rng.randrange(p), rng.randrange(p))
        else:
            m = (yk - yj) * inv(zk - zj, p) % p
            z = rng.randrange(p)
            new[i] = (z, (yj + m * (z - zj)) % p)
    else:
        new[i] = (rng.randrange(p), rng.randrange(p))
    return new


def random_start(p, n, rng):
    mode = rng.randrange(3)
    if mode == 0:
        return [(rng.randrange(p), rng.randrange(p)) for _ in range(n)]
    if mode == 1:
        return mix_config(p, n, rng.randrange(0, n // 2 + 1), rng)
    pool = distinct_points(p, max(2, n // 2), rng)
    return [pool[rng.randrange(len(pool))] for _ in range(n)]


def hill_climb(p, n, a, restarts, iters, budget_s, rng, seeds=()):
    deadline = time.time() + budget_s
    best, best_pts = -1, None
    seedlist = list(seeds)
    r = 0
    while r < restarts and time.time() < deadline:
        pts = list(seedlist[r]) if r < len(seedlist) else random_start(p, n, rng)
        cur = count_bad_points(pts, p, a)
        if cur > best:
            best, best_pts = cur, list(pts)
        for _ in range(iters):
            if time.time() > deadline:
                break
            cand = mutate(pts, p, rng)
            c = count_bad_points(cand, p, a)
            if c >= cur:  # plateau moves allowed
                pts, cur = cand, c
                if cur > best:
                    best, best_pts = cur, list(pts)
        r += 1
    return best, best_pts, r


# ------------------------------------------------------------------------ main
def main():
    a = 3
    print("=" * 78)
    print("probe_dim1_interior_ceiling.py  (constant code, a = 3, n in {8,16})")
    print("=" * 78)

    # ---------------- Phase 0: arithmetic sanity (p = 1 mod n, order-n g exists)
    print("\n--- Phase 0: arithmetic sanity ------------------------------------")
    cfgs = [(17, 8), (41, 8), (113, 8), (17, 16), (97, 16), (113, 16)]
    ok0 = True
    for p, n in cfgs:
        g = order_n_gen(p, n)
        cond = is_prime(p) and p % n == 1 and g is not None
        ok0 &= cond
        info(f"p={p:4d} n={n:2d}: prime={is_prime(p)} p%n={p % n} order-{n} g={g}"
             f"  (domain x_i=g^i exists; irrelevant for constant code)")
    report("P0 arithmetic sanity (p prime, p=1 mod n, order-n generator)", ok0)

    # ---------------- Phase 1: C1 criterion equivalence (3-way, byte-exact sets)
    print("\n--- Phase 1: C1 criterion equivalence (p=17, n=8, a=3) ------------")
    npairs = 520
    mism, nonempty, example = run_c1(17, 8, a, npairs, RNG)
    info(f"{npairs} random pairs (uniform + low-entropy stress), all 17 gammas each, "
         f"3 independent checkers, SET equality")
    info(f"pairs with non-empty bad set: {nonempty}/{npairs}")
    if example is not None:
        u0, u1, A, B, C = example
        print("  COUNTEREXAMPLE (full):")
        print(f"    u0 = {u0}")
        print(f"    u1 = {u1}")
        print(f"    badset subsets-all       = {sorted(A)}")
        print(f"    badset level-set crit    = {sorted(B)}")
        print(f"    badset subsets-in-levels = {sorted(C)}")
        for g in sorted((A | B | C) - (A & B & C)):
            print(f"    gamma={g}: level sets {level_sets(u0, u1, g, 17)}")
    report("C1 three-way byte-exact bad-SET equality", mism == 0, f"mismatches={mism}")
    row("C1 criterion equivalence (520 pairs x 17 gammas)", "0 mismatch",
        f"{mism} mismatch", mism == 0)

    # ----- Phase 1b: bridge between word-level checker and plane-point engine
    bridge_bad = 0
    for _ in range(60):
        u0 = lowent_word(17, 8, RNG)
        u1 = lowent_word(17, 8, RNG)
        pts = [(u1[i], u0[i]) for i in range(8)]
        c_pts = count_bad_points(pts, 17, a)
        c_words = len(badset(bad_by_levelset_criterion, u0, u1, 17, a))
        if c_pts != c_words:
            bridge_bad += 1
    report("P1b word-checker vs plane-point engine #bad agreement (60 pairs)",
           bridge_bad == 0, f"mismatches={bridge_bad}")

    maxima = {}  # (n,p) -> (best, pts, src)

    def upd(n, p, cnt, pts, src):
        key = (n, p)
        if key not in maxima or cnt > maxima[key][0]:
            maxima[key] = (cnt, list(pts), src)

    # ---------------- Phase 2: C3 sharpness families (x doubles + y singletons)
    print("\n--- Phase 2: C3 families: x doubles + y singletons ----------------")
    # certified-generic checks: n=8 at p in {41,113}; n=16 at p=113
    cert_plan = {8: [41, 113], 16: [113]}
    for n in (8, 16):
        bound = (n * n - n) // 4
        for x in range(1, n // 2 + 1):
            formula = x * (x - 1) // 2 + x * (n - 2 * x)
            tag = " (spike, n-2)" if x == 1 else (" (multi-spike)" if x == n // 2 else "")
            for p in cert_plan[n]:
                want = 30 if n == 8 else 12
                cert = certified_mix(p, n, x, RNG, want=want, tries=120_000)
                counts = [count_bad_points(pts, p, a) for pts in cert]
                for pts, c in zip(cert, counts):
                    upd(n, p, c, pts, f"mix x={x} certified")
                exact = all(c == formula for c in counts)
                okf = exact and len(cert) >= 5 and max(counts, default=0) <= bound
                report(f"C3 mix n={n} p={p} x={x}: certified-generic #bad == "
                       f"C(x,2)+x*y == {formula}{tag}",
                       okf, f"({len(cert)} certified, counts={sorted(set(counts))})")
            # unrestricted samples: informational modal/max + maxima feed
            for p in ([17, 41, 113] if n == 8 else [17, 97, 113]):
                counts = []
                for _ in range(50 if n == 8 else 30):
                    pts = mix_config(p, n, x, RNG)
                    c = count_bad_points(pts, p, a)
                    counts.append(c)
                    upd(n, p, c, pts, f"mix x={x}")
                modal = Counter(counts).most_common(1)[0][0]
                info(f"n={n:2d} p={p:4d} x={x}: unrestricted modal={modal:3d} "
                     f"max={max(counts):3d} (formula {formula}"
                     f"{', p=17 caps #bad at 17' if p == 17 and formula > 17 else ''})")
    row("C3 spike n=8 (x=1) certified #bad", "6 (= n-2)", "see mix rows", None)
    row("C3 multi-spike n=8 (x=4) certified #bad", "6 (= C(4,2))", "see mix rows", None)
    row("C3 best mix n=8 (x=2 or 3) certified", "9", "see mix rows", None)
    row("C3 best mix n=16 (x=5) certified", "40", "see mix rows", None)

    # ---------------- Phase 3: designed collinear configs
    print("\n--- Phase 3: designed collinear configs ---------------------------")
    d10_best = {}
    for p in [17, 41, 113]:
        counts = []
        for _ in range(200):
            pts = design10_n8(p, RNG)
            if pts is None:
                continue
            c = count_bad_points(pts, p, a)
            counts.append(c)
            upd(8, p, c, pts, "design10 (x=2 + collinear s-triple)")
        d10_best[p] = max(counts)
        info(f"n= 8 p={p:4d} design10 (2 doubles + collinear s-triple): "
             f"modal={Counter(counts).most_common(1)[0][0]} max={max(counts)} (expect 10)")
    report("C3 design10 reaches 10 at p=113 (beats best generic mix 9)",
           d10_best[113] >= 10, f"max={d10_best[113]}")
    row("C3 designed collinear n=8 (x=2 + s-triple)", "10", str(d10_best[113]),
        d10_best[113] >= 10)

    dq_max = {}
    for p in [97, 113]:
        counts = []
        for _ in range(40):
            pts = design_quadrilateral_n16(p, RNG)
            if pts is None:
                continue
            c = count_bad_points(pts, p, a)
            counts.append(c)
            upd(16, p, c, pts, "design44 (x=5 + complete quadrilateral)")
        dq_max[p] = max(counts)
        info(f"n=16 p={p:4d} design44 (5 doubles + complete-quadrilateral singletons): "
             f"modal={Counter(counts).most_common(1)[0][0]} max={max(counts)} (expect 44)")
    row("C3 designed n=16 (x=5 + quadrilateral)", "44", str(dq_max[113]), None)

    # ---------------- Phase 4: C2 hill-climb max search
    print("\n--- Phase 4: C2 hill-climb max search -----------------------------")
    budgets = {(8, 17): 25, (8, 41): 30, (8, 113): 60,
               (16, 17): 30, (16, 97): 80, (16, 113): 90}
    for n, ps in [(8, [17, 41, 113]), (16, [17, 97, 113])]:
        bound = (n * n - n) // 4
        for p in ps:
            seeds = []
            if (n, p) in maxima:
                seeds.append(maxima[(n, p)][1])
            if n == 8:
                d = design10_n8(p, RNG)
                if d:
                    seeds.append(d)
                seeds.append(mix_config(p, n, 2, RNG))
                seeds.append(mix_config(p, n, 3, RNG))
            else:
                if p > 17:
                    d = design_quadrilateral_n16(p, RNG)
                    if d:
                        seeds.append(d)
                seeds.append(mix_config(p, n, 5, RNG))
                seeds.append(mix_config(p, n, 6, RNG))
            best, best_pts, done = hill_climb(
                p, n, a, restarts=260, iters=260,
                budget_s=budgets[(n, p)], rng=RNG, seeds=seeds)
            upd(n, p, best, best_pts, "hill-climb")
            bb, bpts, bsrc = maxima[(n, p)]
            info(f"n={n:2d} p={p:4d}: hill-climb best={best} (restarts done={done}); "
                 f"overall max={bb} via {bsrc}")
            info(f"           argmax: {fmt_cfg(bpts)}")
            report(f"C2 bound n={n} p={p}: max #bad <= (n^2-n)/4 = {bound}",
                   bb <= bound, f"max={bb}")
            row(f"C2 n={n} p={p} max #bad <= {bound}", f"<= {bound}", str(bb), bb <= bound)

    # KKH26 ceiling comparison (strict)
    print("\n--- KKH26 ceiling comparison --------------------------------------")
    for n, ceil_n, mu in [(8, 24, 3), (16, 112, 4)]:
        mx = max(v[0] for (nn, pp), v in maxima.items() if nn == n)
        report(f"KKH26 pin n={n}: max #bad ({mx}) < ceiling count {ceil_n} (mu={mu}) STRICTLY",
               mx < ceil_n, f"slack={ceil_n - mx}")
        row(f"KKH26 pin n={n}: maxbad < ceiling {ceil_n}", f"< {ceil_n}", str(mx), mx < ceil_n)

    # ---------------- verdict table
    print("\n" + "=" * 78)
    print("VERDICT TABLE  (claim | expected | observed | verdict)")
    print("=" * 78)
    for claim, exp, obs, ok in ROWS:
        v = "PASS" if ok else ("FAIL" if ok is not None else "info")
        print(f"  {claim:<55s} | {exp:>14s} | {obs:>14s} | {v}")
    print(f"\nTotal failures: {FAIL}   elapsed: {elapsed():.1f}s")
    print("MAXIMA SUMMARY:")
    for (n, p), (b, pts, src) in sorted(maxima.items()):
        print(f"  n={n:2d} p={p:4d}: max #bad = {b:3d}  via {src}")
        print(f"      config: {fmt_cfg(pts)}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()

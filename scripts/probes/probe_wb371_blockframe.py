#!/usr/bin/env python3
"""
Block-frame stacks: the census-conjecture stress test (p=12289 + p=17).

Construction: partition-like family of 6-point agreement blocks A_i with
deg<3 polys q_i (for R1) and frames r_i (for R0), compatible on overlaps;
R1 := interp(q_i on A_i, free elsewhere), R0 := interp(r_i on A_i, free).
Then for EVERY block A_i and every x not in A_i with R1(x) != q_i(x):
S = A_i + {x} is explainable for the single gamma_x =
-(R0(x)-r_i(x))/(R1(x)-q_i(x)), and (generically) not-joint => BAD.
Cross-block scalars trace gamma = -f(x), f = (r_j - r_i)/(q_j - q_i):
a deg-2/deg-2 rational -- injectivity on 12 points is generically possible,
PREDICTING ~20 distinct bad scalars for 2 disjoint blocks: ABOVE the census
record 16.  The 4-block design (pairwise <=2 overlaps, union = domain)
has 40 candidates: if > 31 distinct realizable, the round-7 obligation
SubCeilingInteriorCeiling <= 31 is FALSE.

This probe builds both designs (with random steering retries), runs the
EXACT census (per 7-subset residue alignment over all C(16,7) subsets,
joint-clause faithful), and reports the maximum total bad count.
"""
import itertools, random

def make_field_tools(p, n):
    g0 = next(g for g in range(2, 500)
              if all(pow(g, (p - 1) // f, p) != 1
                     for f in set(x for x in (2, 3, 5, 7, 257)
                                  if (p - 1) % x == 0)))
    w = pow(g0, (p - 1) // n, p)
    assert pow(w, n, p) == 1 and all(pow(w, j, p) != 1 for j in range(1, n))
    D = [pow(w, j, p) for j in range(n)]
    def polmul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] = (out[i + j] + x * y) % p
        return out
    def peval(f, x):
        r = 0
        for c in reversed(f):
            r = (r * x + c) % p
        return r
    def interp(pts, vals):
        m = len(pts)
        coeffs = [0] * m
        for i in range(m):
            num = [1]
            den = 1
            for j in range(m):
                if j == i:
                    continue
                num = polmul(num, [(-pts[j]) % p, 1])
                den = den * ((pts[i] - pts[j]) % p) % p
            ci = vals[i] * pow(den, p - 2, p) % p
            for t in range(len(num)):
                coeffs[t] = (coeffs[t] + ci * num[t]) % p
        return coeffs
    return D, peval, interp

def census(p, n, s, D, interp, u0, u1):
    bad = {}
    for S in itertools.combinations(range(n), s):
        pts = [D[i] for i in S]
        a = interp(pts, [u0[i] for i in S])
        b = interp(pts, [u1[i] for i in S])
        ta = [a[t] if t < len(a) else 0 for t in range(3, s)]
        tb = [b[t] if t < len(b) else 0 for t in range(3, s)]
        if all(x == 0 for x in tb):
            continue  # u1|S low-deg: either joint or no unique gamma target
        j = next(t for t in range(len(tb)) if tb[t])
        gam = (-ta[j]) * pow(tb[j], p - 2, p) % p
        if all((ta[t] + gam * tb[t]) % p == 0 for t in range(len(tb))):
            bad.setdefault(gam, []).append(S)
    return bad

def two_block(p, tries, seed):
    n, s = 16, 7
    D, peval, interp = make_field_tools(p, n)
    A1, A2 = list(range(0, 6)), list(range(6, 12))
    FREE = list(range(12, 16))
    best = 0
    for t in range(tries):
        rng = random.Random(seed + t)
        q1 = [rng.randrange(p) for _ in range(3)]
        q2 = [rng.randrange(p) for _ in range(3)]
        r1 = [rng.randrange(p) for _ in range(3)]
        r2 = [rng.randrange(p) for _ in range(3)]
        u1 = [0] * n
        u0 = [0] * n
        for i in A1:
            u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
        for i in A2:
            u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
        # steer the free points: pick target gammas, solve (R0,R1)(x)
        for i in FREE:
            g_a = rng.randrange(1, p)   # gamma for block-1 witness at i
            g_b = rng.randrange(1, p)   # gamma for block-2 witness at i
            if g_a == g_b:
                g_b = (g_b + 1) % p or 1
            # R0+ga*R1 = r1+ga*q1 at x ; R0+gb*R1 = r2+gb*q2 at x
            x = D[i]
            rhs1 = (peval(r1, x) + g_a * peval(q1, x)) % p
            rhs2 = (peval(r2, x) + g_b * peval(q2, x)) % p
            det = (g_a - g_b) % p
            R1x = (rhs1 - rhs2) * pow(det, p - 2, p) % p
            R0x = (rhs1 - g_a * R1x) % p
            u1[i] = R1x; u0[i] = R0x
        bad = census(p, n, s, D, interp, u0, u1)
        if len(bad) > best:
            best = len(bad)
            wit = sorted(len(v) for v in bad.values())
            print(f"  [2-block p={p}] try {t}: total bad = {len(bad)} "
                  f"(witness-counts tail {wit[-4:]})")
    return best

def four_block(p, tries, seed):
    n, s = 16, 7
    D, peval, interp = make_field_tools(p, n)
    A = [list(range(0, 6)), list(range(6, 12)),
         [0, 1, 6, 7, 12, 13], [2, 3, 8, 9, 14, 15]]
    best = 0
    for t in range(tries):
        rng = random.Random(seed + t)
        ok = False
        for _ in range(200):
            q3 = [rng.randrange(p) for _ in range(3)]
            r3 = [rng.randrange(p) for _ in range(3)]
            # q1 == q3 on pts {0,1}: 2 constraints, 1 free dof (deg<3)
            def fit_through(base, idxs, dof_val):
                # poly deg<3 through (D[i], peval(base,D[i])) for i in idxs,
                # plus value dof_val at a fresh anchor point D[15]+1 trick:
                pts = [D[i] for i in idxs]
                vals = [peval(base, x) for x in pts]
                # third condition: coefficient steering via extra point 1+max
                xa = (max(pts) + 1) % p
                while xa in pts:
                    xa = (xa + 1) % p
                return interp(pts + [xa], vals + [dof_val])
            q1 = fit_through(q3, [0, 1], rng.randrange(p))
            r1 = fit_through(r3, [0, 1], rng.randrange(p))
            q2 = fit_through(q3, [6, 7], rng.randrange(p))
            r2 = fit_through(r3, [6, 7], rng.randrange(p))
            # q4 must agree with q1 on {2,3} and q2 on {8,9}: 4 pts, deg<3
            pts4 = [D[i] for i in [2, 3, 8, 9]]
            v4 = [peval(q1, D[2]), peval(q1, D[3]),
                  peval(q2, D[8]), peval(q2, D[9])]
            c4 = interp(pts4, v4)
            if len(c4) > 3 and any(c4[3:]):
                continue  # not deg<3 -- resample
            q4 = c4[:3] + [0] * (3 - len(c4[:3]))
            pr4 = [peval(r1, D[2]), peval(r1, D[3]),
                   peval(r2, D[8]), peval(r2, D[9])]
            cr4 = interp(pts4, pr4)
            if len(cr4) > 3 and any(cr4[3:]):
                continue
            r4 = cr4[:3] + [0] * (3 - len(cr4[:3]))
            ok = True
            break
        if not ok:
            continue
        qs, rs = [q1, q2, q3, r4 and q4], [r1, r2, r3, r4]
        qs = [q1, q2, q3, q4]
        u0, u1 = [0] * n, [0] * n
        owner = {}
        for bi, blk in enumerate(A):
            for i in blk:
                if i in owner:
                    continue
                owner[i] = bi
                u1[i] = peval(qs[bi], D[i])
                u0[i] = peval(rs[bi], D[i])
        bad = census(p, n, s, D, interp, u0, u1)
        if len(bad) > best:
            best = len(bad)
            print(f"  [4-block p={p}] try {t}: total bad = {len(bad)}")
    return best

if __name__ == "__main__":
    b17 = two_block(17, 30, 50)
    b2 = two_block(12289, 25, 99)
    b4 = four_block(12289, 25, 777)
    print(f"RESULTS: 2-block p=17 max {b17}; 2-block p=12289 max {b2}; "
          f"4-block p=12289 max {b4}")
    print(f"census record 16; obligation 31")

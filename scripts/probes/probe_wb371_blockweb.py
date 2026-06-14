#!/usr/bin/env python3
"""
Block-web maximization (p=12289): how many distinct bad scalars can
k-block frame webs realize?  2-block already gives 20 > census record 16.
If any web realizes >= 32, the round-7 obligation
SubCeilingInteriorCeiling <= 31 is FALSE.

Exact parametrization (all deg<3 conditions solved algebraically):
  blocks A_i (|A|=6, pairwise share <= 2), base poly q on block 1;
  q_i = q + c_i * Z_i where Z_i = prod over shared pts with EARLIER blocks
  (X - x).  For a block sharing 2 pts with TWO earlier blocks (4 constraint
  points), c_i is solved linearly from the one compatibility equation.
  Same independently for r_i (R0 side).  R1 := values q_i on A_i (consistent
  on overlaps), free values steered at uncovered points; R0 likewise.
Census: exact per-7-subset residue alignment (joint-faithful).
Designs probed:
  W2: A1,A2 disjoint + 4 free points (validated 20)
  W3: A1,A2 disjoint + A3 sharing 2+2, 4 free points re-steered
  W4: the 2+2+2+2 web covering all 16
  W3F: 3 blocks pairwise sharing 2 (union 14) + 2 free
"""
import itertools, random

p, n, s = 12289, 16, 7

def make():
    g0 = next(g for g in range(2, 500)
              if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
    w = pow(g0, (p - 1) // n, p)
    D = [pow(w, j, p) for j in range(n)]
    return D

D = make()

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
        num = [1]; den = 1
        for j in range(m):
            if j == i:
                continue
            num = polmul(num, [(-pts[j]) % p, 1])
            den = den * ((pts[i] - pts[j]) % p) % p
        ci = vals[i] * pow(den, p - 2, p) % p
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + ci * num[t]) % p
    return coeffs

def census(u0, u1):
    bad = {}
    for S in itertools.combinations(range(n), s):
        pts = [D[i] for i in S]
        a = interp(pts, [u0[i] for i in S])
        b = interp(pts, [u1[i] for i in S])
        ta = [a[t] if t < len(a) else 0 for t in range(3, s)]
        tb = [b[t] if t < len(b) else 0 for t in range(3, s)]
        if all(x == 0 for x in tb):
            continue
        j = next(t for t in range(len(tb)) if tb[t])
        gam = (-ta[j]) * pow(tb[j], p - 2, p) % p
        if all((ta[t] + gam * tb[t]) % p == 0 for t in range(len(tb))):
            bad.setdefault(gam, []).append(S)
    return bad

def solve_web(blocks, rng):
    """assign deg<3 polys per block, consistent on pairwise overlaps.
    Greedy: block 0 free; each later block: q_i = correction through the
    constraint points (shared with already-assigned blocks).  Constraint
    points <= 3: free interpolation + free dof; == 4: linear solve for the
    last param via the X-Z parametrization.  Returns list of coeff vectors
    or None."""
    polys = []
    for bi, A in enumerate(blocks):
        cons = []  # (x, value) constraints from earlier blocks
        for bj in range(bi):
            for i in set(A) & set(blocks[bj]):
                cons.append((D[i], peval(polys[bj], D[i])))
        cons = list(dict(cons).items())
        if len(cons) == 0:
            polys.append([rng.randrange(p) for _ in range(3)])
        elif len(cons) <= 3:
            # interpolate constraints + random values at extra anchors
            pts = [x for x, _ in cons]
            vals = [v for _, v in cons]
            while len(pts) < 3:
                xa = rng.randrange(1, p)
                if xa not in pts:
                    pts.append(xa); vals.append(rng.randrange(p))
            polys.append(interp(pts, vals))
        elif len(cons) == 4:
            # q = interp through first 3 + c * Z, Z = prod (X - x_j), j<3;
            # c solved from 4th constraint (Z(x4) != 0 generically)
            pts3 = [x for x, _ in cons[:3]]
            vals3 = [v for _, v in cons[:3]]
            base = interp(pts3, vals3)
            x4, v4 = cons[3]
            Z = [1]
            for x in pts3:
                Z = polmul(Z, [(-x) % p, 1])
            Zx4 = peval(Z, x4)
            if Zx4 == 0:
                return None
            c = (v4 - peval(base, x4)) * pow(Zx4, p - 2, p) % p
            q = [0, 0, 0, 0]
            for t, cf in enumerate(base):
                q[t] = cf
            for t, cf in enumerate(Z):
                q[t] = (q[t] + c * cf) % p
            if q[3] % p:
                return None  # needs the cubic term: infeasible draw
            polys.append(q[:3])
        else:
            return None
    return polys

def run_design(name, blocks, tries, steer_free, seed):
    best, bestbad = 0, None
    covered = sorted(set().union(*[set(b) for b in blocks]))
    free = [i for i in range(n) if i not in covered]
    for t in range(tries):
        rng = random.Random(seed + t)
        qs = solve_web(blocks, rng)
        rs = solve_web(blocks, rng)
        if qs is None or rs is None:
            continue
        u0, u1 = [None] * n, [None] * n
        for bi, A in enumerate(blocks):
            for i in A:
                u1[i] = peval(qs[bi], D[i])
                u0[i] = peval(rs[bi], D[i])
        for i in free:
            if steer_free and len(blocks) >= 2:
                ga, gb = rng.randrange(1, p), rng.randrange(1, p)
                if ga == gb:
                    gb = gb % (p - 1) + 1
                x = D[i]
                rhs1 = (peval(rs[0], x) + ga * peval(qs[0], x)) % p
                rhs2 = (peval(rs[1], x) + gb * peval(qs[1], x)) % p
                det = (ga - gb) % p
                R1x = (rhs1 - rhs2) * pow(det, p - 2, p) % p
                u1[i] = R1x
                u0[i] = (rhs1 - ga * R1x) % p
            else:
                u1[i] = rng.randrange(p)
                u0[i] = rng.randrange(p)
        bad = census(u0, u1)
        if len(bad) > best:
            best = len(bad)
            bestbad = (u0[:], u1[:], sorted(bad))
            print(f"  [{name}] try {t}: total bad = {len(bad)}")
    if bestbad and best > 31:
        print(f"  [{name}] OBLIGATION-BREAKER stack: u0={bestbad[0]} "
              f"u1={bestbad[1]}")
    return best

A1 = list(range(0, 6))
A2 = list(range(6, 12))
A3w = [0, 1, 6, 7, 12, 13]
A4w = [2, 3, 8, 9, 14, 15]
A3f = [0, 1, 6, 7, 12, 13]

if __name__ == "__main__":
    r2 = run_design("W2 2-block", [A1, A2], 12, True, 11)
    r3 = run_design("W3 3-block+free", [A1, A2, A3f], 25, False, 22)
    r4 = run_design("W4 4-block-full", [A1, A2, A3w, A4w], 40, False, 33)
    print(f"RESULTS: W2={r2} W3={r3} W4={r4}; record-to-beat 20; "
          f"obligation threshold 31")

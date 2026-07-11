#!/usr/bin/env python3
"""
Independent double-verification of the 2-block 20-bad-scalar stack
(p=12289, n=16, k=3, agreement 7) that refutes the bad<=16 census record.

Builds the deterministic 2-block stack (seed-fixed), then checks badness of
every scalar by TWO independent methods:
  (1) fast residue-alignment census (per 7-subset interpolant top-coeffs);
  (2) slow Lagrange-fit explainability + joint-clause check per subset
      (the probe_pool_construct-style checker).
Methods must agree exactly; prints the stack and the 20 scalars.
"""
import itertools, random

p, n, s, k = 12289, 16, 7, 3

g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
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

# --- the deterministic 2-block stack ---
rng = random.Random(20260612)
A1, A2 = list(range(0, 6)), list(range(6, 12))
FREE = [12, 13, 14, 15]
q1 = [rng.randrange(p) for _ in range(3)]
q2 = [rng.randrange(p) for _ in range(3)]
r1 = [rng.randrange(p) for _ in range(3)]
r2 = [rng.randrange(p) for _ in range(3)]
u0, u1 = [0] * n, [0] * n
for i in A1:
    u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
for i in A2:
    u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
target = [(101 + 7 * t, 4001 + 13 * t) for t in range(4)]
for (ga, gb), i in zip(target, FREE):
    x = D[i]
    rhs1 = (peval(r1, x) + ga * peval(q1, x)) % p
    rhs2 = (peval(r2, x) + gb * peval(q2, x)) % p
    R1x = (rhs1 - rhs2) * pow((ga - gb) % p, p - 2, p) % p
    u1[i] = R1x; u0[i] = (rhs1 - ga * R1x) % p

# --- method 1: fast residue census ---
bad1 = {}
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
        bad1.setdefault(gam, []).append(S)

# --- method 2: slow Lagrange-fit checker on method-1 scalars + controls ---
def fits_lowdeg(S, vals):
    base = list(zip([D[i] for i in S], vals))[:k]
    def evalL(x):
        tot = 0
        for i, (xi, yi) in enumerate(base):
            num, den = 1, 1
            for j, (xj, _) in enumerate(base):
                if i == j:
                    continue
                num = num * ((x - xj) % p) % p
                den = den * ((xi - xj) % p) % p
            tot = (tot + yi * num * pow(den, p - 2, p)) % p
        return tot
    return all(evalL(D[i]) == v % p
               for i, v in list(zip(S, vals))[k:])

def is_bad_slow(g):
    for S in itertools.combinations(range(n), s):
        fold = [(u0[i] + g * u1[i]) % p for i in S]
        if not fits_lowdeg(S, fold):
            continue
        if fits_lowdeg(S, [u0[i] for i in S]) and \
           fits_lowdeg(S, [u1[i] for i in S]):
            continue
        return True
    return False

claimed = sorted(bad1)
controls = [g for g in range(7, 7 + 40) if g not in bad1][:25]
ok = all(is_bad_slow(g) for g in claimed)
ok2 = not any(is_bad_slow(g) for g in controls)
print(f"fast census: {len(claimed)} bad scalars")
print(f"slow checker confirms all {len(claimed)}: {ok}; "
      f"25 random non-bad controls clean: {ok2}")
print(f"VERDICT: {'CONFIRMED' if ok and ok2 and len(claimed) > 16 else 'CHECK'}"
      f" -- {len(claimed)} > 16 census record" if ok and ok2 else "MISMATCH")
print(f"stack u0={u0}")
print(f"stack u1={u1}")
print(f"bad scalars: {claimed}")

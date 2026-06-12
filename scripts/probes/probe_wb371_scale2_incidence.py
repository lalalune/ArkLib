#!/usr/bin/env python3
"""
Scale-2 probe at (q,n,k,w) = (13,12,1,4): D = mu_12 = F_13^*.
First window scale: n = 3w, deg L = 2w = 8, m_S deg = n-w = 8, S in C(12,8) (495),
quotient P^{2w-1} = P^7.

Tests:
 (A) The core+pairs construction: K (w-2=2 points) + all 6 pairs of a 4-set W'
     => 6 vanishing-classes m_S in one 3-space (predicted).  Verify rank == 3
     (with suitable L in the space, rank{m's} <= 3 already in POLY space).
 (B) MaxCollinear(Sigma_L) for sampled realizable L = l0*l1 (monic quartics,
     including sigma-symmetric ones) and random monic deg-8: does anything
     exceed 6?  (span-hash O(N^2) per L)
 (C) Faithful mcaEvent bad-count by stratum at radius w/n = 1/3:
     genuine x genuine, pole x genuine, pole x pole.  Cap vs w+1 = 5?
"""
import itertools, random

q, n, k, w = 13, 12, 1, 4
NW = n - w        # 8
D = list(range(1, 13))   # mu_12 = all of F_13^*
need = n - w      # agreement floor

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def m_of(S):
    out = [1]
    for x in S:
        out = polmul(out, [(-x) % q, 1])
    return out

def rank_of(rows, width):
    M = [list(r) + [0] * (width - len(r)) for r in rows]
    r = 0
    for col in range(width):
        piv = None
        for row in range(r, len(M)):
            if M[row][col] % q:
                piv = row; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        invp = pow(M[r][col], q - 2, q)
        for row in range(len(M)):
            if row != r and M[row][col] % q:
                f = (M[row][col] * invp) % q
                for cc in range(width):
                    M[row][cc] = (M[row][cc] - f * M[r][cc]) % q
        r += 1
    return r

# ---------------- (A) core+pairs: rank of the 6 m_S in POLY space -------------
random.seed(3)
print("=== (A) core+pairs construction at w=4 ===")
for trial in range(4):
    pts = random.sample(D, 6)
    K = pts[:2]; W4 = pts[2:]
    fam = []
    for pair in itertools.combinations(W4, 2):
        T = sorted(K + list(pair))
        S = sorted(set(D) - set(T))
        fam.append(m_of(S))
    rk = rank_of(fam, 9)
    print(f"  K={K} W'={W4}: rank of 6 m_S (in F^9) = {rk}  (predicted 3)")

# ---------------- (B) MaxCollinear over L --------------------------------------
def vec_mod_L(poly, L):
    # quotient F[X]_{<=8} / <L>, L monic deg 8: canonical rep kills X^8 coeff
    p = [x % q for x in poly] + [0] * (9 - len(poly))
    p = p[:9]
    c = p[8] % q   # L monic
    return tuple((p[i] - c * L[i]) % q for i in range(8))

def proj_norm(v):
    for x in v:
        if x % q:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    return None

SUBS = list(itertools.combinations(D, NW))   # 495
MS = {S: m_of(S) for S in SUBS}

def max_collinear_for(L, report=False):
    pts = {}
    for S in SUBS:
        pn = proj_norm(vec_mod_L(MS[S], L))
        if pn is not None:
            pts.setdefault(pn, []).append(S)
    P = list(pts.keys())
    best = 1; bestpair = None
    # span-hash: for each anchor a, canonical form of span(a,b)
    for ia in range(len(P)):
        a = P[ia]
        seen = {}
        for ib in range(len(P)):
            if ib == ia: continue
            b = P[ib]
            # canonicalize span(a,b): RREF of 2x8
            M = [list(a), list(b)]
            # manual 2-row RREF over F_q
            rows = rref2(M)
            key = tuple(map(tuple, rows))
            seen[key] = seen.get(key, 0) + 1
        if seen:
            mx = max(seen.values()) + 1   # +1 for the anchor
            if mx > best:
                best = mx; bestpair = (a,)
    return best, pts

def rref2(M):
    M = [r[:] for r in M]
    r = 0
    for col in range(8):
        piv = None
        for row in range(r, 2):
            if M[row][col] % q: piv = row; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        invp = pow(M[r][col], q - 2, q)
        M[r] = [(x * invp) % q for x in M[r]]
        for row in range(2):
            if row != r and M[row][col] % q:
                f = M[row][col]
                M[row] = [(M[row][i] - f * M[r][i]) % q for i in range(8)]
        r += 1
        if r == 2: break
    return M

print("\n=== (B) MaxCollinear over sampled L (deg 8 monic) ===")
dist = {}
worst = (0, None)
NL = 60
for trial in range(NL):
    if trial % 3 == 0:
        # realizable: product of two monic quartics
        l0 = [random.randrange(q) for _ in range(4)] + [1]
        l1 = [random.randrange(q) for _ in range(4)] + [1]
        L = polmul(l0, l1); tag = "l0*l1"
    elif trial % 3 == 1:
        L = [random.randrange(q) for _ in range(8)] + [1]; tag = "random"
    else:
        # core+pairs special: L = m_K-shifted partial-fraction element:
        # L = sum_e lam_e (X^12-1)/(m_K (X-e)) with sum lam = 0... construct in
        # poly space: take two members of the family and a random combo (monic'd)
        pts6 = random.sample(D, 6); K = pts6[:2]; W4 = pts6[2:]
        pairs = list(itertools.combinations(W4, 2))
        f1 = m_of(sorted(set(D) - set(K) - set(pairs[0])))
        f2 = m_of(sorted(set(D) - set(K) - set(pairs[1])))
        a = random.randrange(1, q)
        L = [(x + a * y) % q for x, y in zip(f1 + [0]*(9-len(f1)), f2 + [0]*(9-len(f2)))]
        if L[8] % q == 0:
            L[8] = 1  # fallback degenerate
        else:
            inv = pow(L[8], q-2, q); L = [(x*inv)%q for x in L]
        tag = "V0-special"
    mc, _ = max_collinear_for(L)
    dist.setdefault(tag, {}).setdefault(mc, 0)
    dist[tag][mc] += 1
    if mc > worst[0]:
        worst = (mc, L, tag)
for tag in dist:
    print(f"  {tag}: {dict(sorted(dist[tag].items()))}")
print(f"  WORST: MaxCollinear={worst[0]} ({worst[2]})")

# ---------------- (C) faithful mcaEvent by stratum ------------------------------
print("\n=== (C) faithful bad-count by stratum ===")
SUBSETS_GE = []
for r in range(need, n + 1):
    SUBSETS_GE.extend(itertools.combinations(range(n), r))
print(f"  witness sets: {len(SUBSETS_GE)}")

def joint_on_S(u0, u1, S):
    return len({u0[i] for i in S}) == 1 and len({u1[i] for i in S}) == 1

def line_const_on_S(u0, u1, g, S):
    it = iter(S)
    i0 = next(it)
    v = (u0[i0] + g * u1[i0]) % q
    return all((u0[i] + g * u1[i]) % q == v for i in it)

def is_bad(u0, u1, g):
    for S in SUBSETS_GE:
        if line_const_on_S(u0, u1, g, S) and not joint_on_S(u0, u1, S):
            return True
    return False

def bad_count(u0, u1):
    return sum(1 for g in range(q) if is_bad(u0, u1, g))

def poleval(p, x):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def rand_genuine():
    """rational R/l with l irreducible-ish: no roots in D (=F13*), l(0) can be anything"""
    while True:
        l = [random.randrange(q) for _ in range(w)] + [1]
        if all(poleval(l, x) for x in D):
            R = [random.randrange(q) for _ in range(w + k)]
            u = tuple((poleval(R, x) * pow(poleval(l, x), q - 2, q)) % q for x in D)
            return u

def rand_pole():
    """l with some roots in D: u = R/l off roots, arbitrary at roots"""
    roots = random.sample(D, random.randrange(1, w + 1))
    l = [1]
    for r0 in roots:
        l = polmul(l, [(-r0) % q, 1])
    while len(l) - 1 < w:
        l = polmul(l, [random.randrange(q), 1])  # extra linear factors (may add D-roots)
    R = [random.randrange(q) for _ in range(w + k)]
    u = []
    for x in D:
        lx = poleval(l, x)
        if lx == 0:
            u.append(random.randrange(q))
        else:
            u.append((poleval(R, x) * pow(lx, q - 2, q)) % q)
    return tuple(u)

random.seed(5)
for tag, gen0, gen1, NS in [("genuine x genuine", rand_genuine, rand_genuine, 1500),
                            ("pole x genuine", rand_pole, rand_genuine, 1500),
                            ("pole x pole", rand_pole, rand_pole, 1500)]:
    mx = 0; arg = None
    for _ in range(NS):
        u0, u1 = gen0(), gen1()
        b = bad_count(u0, u1)
        if b > mx:
            mx = b; arg = (u0, u1)
    print(f"  {tag}: max bad over {NS} samples = {mx}  (w+1={w+1}, w+3={w+3})")
    if arg and mx >= 3:
        print(f"      witness u0={arg[0]} u1={arg[1]}")

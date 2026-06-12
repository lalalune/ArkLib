#!/usr/bin/env python3
"""
Probe: the projective-incidence reformulation of WindowRationalBounded
at the first window scale, k=1.

Setup (q,n,k,w) = (13,6,1,2):  D = mu_6 in F_13, D_def = 3w+k-1-n = 0.
Quotient V = F[X]_{<=2w+k-1} / (L * F[X]_{<k}) = F[X]_{<=4} / <L>,  dim 4, P^3.
Sigma_L = { [m_S mod L] : S subset of D, |S| = n-w = 4 }   (15 points).

Claims to test:
 (1) Semantic match: for the probe extremal stack, the mcaEvent-bad gammas are
     exactly the gammas with  A + gamma*B == p*L + c*m_S  for some S (deg-counting),
     i.e. line-points on Sigma_L.  (Upper-bound direction is what matters.)
 (2) MaxCollinear(Sigma_L) over ALL lines in P^3, for many L: is it <= w+3? w+1?
 (3) Structure of maximizing configurations (complementary w-sets T = D\\S:
     sigma-orbit / coset patterns?).
"""
import itertools, random

q, n, k, w = 13, 6, 1, 2
NW = n - w           # 4  (size of S)
DEGL = 2 * w         # 4
DIM = 2 * w + k      # 5 coefficients (deg <= 4); quotient dim 4

def order_subgroup(q, n):
    for cand in range(2, q):
        seen = set(); x = 1
        for _ in range(q - 1):
            x = (x * cand) % q; seen.add(x)
        if len(seen) == q - 1:
            g = cand; break
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, j, q) for j in range(n)})

D = order_subgroup(q, n)
SUBS = list(itertools.combinations(D, NW))   # 15 agreement supports

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def poldivmod(a, b):
    # a, b coefficient lists (low->high), b != 0; returns (quot, rem)
    a = a[:]
    db = max(i for i in range(len(b)) if b[i] % q)
    inv = pow(b[db], q - 2, q)
    quot = [0] * max(1, len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % q
        if c:
            f = (c * inv) % q
            quot[i - db] = f
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % q
    return quot, [x % q for x in a[:db]] + [0] * 0

def m_of(S):
    out = [1]
    for x in S:
        out = polmul(out, [(-x) % q, 1])
    return out

def vec_of(poly, L):
    """image of poly in F[X]_{<=4} mod <L>: reduce deg, then subtract multiple of L
       to kill... careful: quotient by the 1-dim space <L> inside deg<=4. We
       represent classes by reducing mod L as polynomials (poldivmod), giving a
       deg<=3 representative -- BUT that conflates p ~ p + h*L with deg h > 0,
       which is NOT in the quotient for k=1 (only scalar multiples of L).
       For deg(poly) <= 4 and deg L = 4: poly mod <L> as vector space = poly - c*L
       where c = lead coeff ratio; canonical rep = kill the X^4 coefficient.
       (Valid iff deg L = 4 exactly.)"""
    p = [x % q for x in poly] + [0] * (DIM - len(poly))
    p = p[:DIM]
    if len(poly) > DIM and any(x % q for x in poly[DIM:]):
        raise ValueError("degree too big")
    c = (p[4] * pow(L[4], q - 2, q)) % q
    return tuple((p[i] - c * L[i]) % q for i in range(4))

def proj_norm(v):
    """projective normalization of a nonzero vector in F^4."""
    for x in v:
        if x % q:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    return None  # zero vector

def sigma_points(L):
    pts = {}
    for S in SUBS:
        mv = vec_of(m_of(S), L)
        pn = proj_norm(mv)
        if pn is not None:
            pts.setdefault(pn, []).append(S)
    return pts  # proj point -> list of S mapping there

def max_collinear(pts_dict):
    pts = list(pts_dict.keys())
    if len(pts) <= 2:
        return len(pts), pts
    best = (2, None)
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            # count points on projective line span(pts[i], pts[j])
            cnt = 0
            members = []
            for p in pts:
                # p in span(a,b)? rank of 3x4 matrix <= 2
                if rank3(pts[i], pts[j], p) <= 2:
                    cnt += 1
                    members.append(p)
            if cnt > best[0]:
                best = (cnt, members)
    return best

def rank3(a, b, c):
    M = [list(a), list(b), list(c)]
    r = 0
    for col in range(4):
        piv = None
        for row in range(r, 3):
            if M[row][col] % q:
                piv = row; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        invp = pow(M[r][col], q - 2, q)
        for row in range(3):
            if row != r and M[row][col] % q:
                f = (M[row][col] * invp) % q
                for cc in range(4):
                    M[row][cc] = (M[row][cc] - f * M[r][cc]) % q
        r += 1
    return r

# --------------------------------------------------------------------------
# (1) semantic check on the probe extremal:
# u0 spike: l0 = (X-9)(X-10), R0 = 0 ... wait R0=0 makes A=0; recall probe reps:
# u0 = (0,0,0,1,1,0) had rep l0=(12,7,1) -> 12+7X+X^2, R0 = 0.
# u1 = (0,1,1,2,2,0) rep l1=(12,11,1), R1=(3,0,10) -> 3+10X^2.
l0 = [12, 7, 1]; R0 = [0]
l1 = [12, 11, 1]; R1 = [3, 0, 10]
L = polmul(l0, l1)          # deg 4
A = polmul(R0, l1)          # = 0
B = polmul(R1, l0)          # deg 4
print("L =", L, " A =", A, " B =", B)

# bad gammas from the earlier faithful probe: {0, 6, 12}
# incidence prediction: gamma bad(-upper) iff vec(A + gamma*B) lies on some [m_S]
ptsL = sigma_points(L)
print(f"|Sigma_L| = {len(ptsL)} distinct projective points (of {len(SUBS)} S's)")
Avec = vec_of(A + [0]*(5-len(A)), L) if len(A) <= 5 else None
hits = {}
for g in range(q):
    AB = [(A[i] if i < len(A) else 0) + g * (B[i] if i < len(B) else 0) for i in range(5)]
    v = vec_of(AB, L)
    pn = proj_norm(v)
    if pn is None:
        hits[g] = "ZERO-CLASS (A+gB in <L>)"
    elif pn in ptsL:
        hits[g] = ("HIT", ptsL[pn][:3])
print("incidence hits by gamma:", {g: h for g, h in hits.items()})

# --------------------------------------------------------------------------
# (2) MaxCollinear over many L
random.seed(11)
def random_L():
    # random monic deg-4, possibly with structure: half the time product of two
    # random monic quadratics (the realizable shape l0*l1)
    if random.random() < 0.5:
        a = [random.randrange(q), random.randrange(q), 1]
        b = [random.randrange(q), random.randrange(q), 1]
        return polmul(a, b)
    return [random.randrange(q) for _ in range(4)] + [1]

dist = {}
worst = (0, None)
for trial in range(4000):
    Lr = random_L()
    pts = sigma_points(Lr)
    mc, members = max_collinear(pts)
    dist[mc] = dist.get(mc, 0) + 1
    if mc > worst[0]:
        worst = (mc, Lr, members, pts)
print("\nMaxCollinear distribution over 4000 random L:", dict(sorted(dist.items())))
print("worst L:", worst[1], "MaxCollinear =", worst[0])
if worst[0] > 2 and worst[2]:
    print("collinear point membership (their S-sets):")
    for p in worst[2]:
        Ss = worst[3][p]
        print("   point", p, "<- S:", [tuple(S) for S in Ss], " T=D\\S:",
              [tuple(sorted(set(D) - set(S))) for S in Ss])

# the extremal's own L:
mcE, memE = max_collinear(ptsL)
print("\nextremal L MaxCollinear =", mcE)
if memE:
    for p in memE:
        print("   point", p, "T=D\\S:", [tuple(sorted(set(D)-set(S))) for S in ptsL[p]])

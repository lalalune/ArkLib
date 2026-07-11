#!/usr/bin/env python3
"""
Pool-pair construction probe (p=12289, n=16, k=3, |S|=7).

By pool_pair_span, a pool pair (two bad scalars with witness overlap <= 3,
not agreement-attached) DETERMINES the stack:
   R1 = (g1*m_S1 - g2*m_S2 + (P1-P2)) / (gamma1 - gamma2)
   R0 = g1*m_S1 + P1 - gamma1*R1.
Conversely: CHOOSE (S1, S2, g1, g2, P1, P2, gamma1, gamma2) with
|S1 ∩ S2| <= 3, build (R0, R1), and faithfully check whether BOTH gammas are
actually bad (the identities hold by construction => both are EXPLAINABLE;
badness additionally needs the no-joint clause - check it).

If both gammas are genuinely bad on many random constructions: pool pairs
EXIST and the pool bound needs real counting. If the joint clause (or
degree degeneration) kills them systematically: the pool is empty/tiny by
construction - closing the rung ledger.
Also measure: the agreement-geometry of the constructed R1 on S1, S2
(does construction secretly create attachment?).
"""
import itertools, random

p, n, k = 12289, 16, 3

def mu_n():
    for g in range(2, 300):
        if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)):
            h = pow(g, (p - 1) // n, p)
            return sorted(pow(h, j, p) for j in range(n))
    raise RuntimeError

D = mu_n()

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % p, 1])
    return out

def poleval(f, x):
    return sum(c * pow(x, i, p) for i, c in enumerate(f)) % p

def padd(a, b, s=1):
    m = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + s * (b[i] if i < len(b) else 0)) % p
            for i in range(m)]

def lagrange_fits(pts, vals, deg):
    base = list(zip(pts, vals))[:deg + 1]
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
    return all(evalL(x) == y % p for x, y in list(zip(pts, vals))[deg + 1:])

SUBS7 = list(itertools.combinations(range(n), 7))

def is_bad_faithful(u0, u1, g):
    for S in SUBS7:
        pts = [D[i] for i in S]
        lvals = [(u0[i] + g * u1[i]) % p for i in S]
        if not lagrange_fits(pts, lvals, k - 1):
            continue
        # explainable on S; joint?
        if lagrange_fits(pts, [u0[i] for i in S], k - 1) and \
           lagrange_fits(pts, [u1[i] for i in S], k - 1):
            continue  # joint: S can't witness
        return True
    return False

random.seed(151)
exist = 0
joint_killed = 0
deg_killed = 0
attach_created = 0
TR = 60
for trial in range(TR):
    # disjoint-ish witness sets
    overlap = random.choice([0, 1, 2, 3])
    pts = random.sample(range(n), 14 - overlap)
    S1 = sorted(pts[:7])
    S2 = sorted(pts[7 - overlap:14 - overlap])
    g1 = [random.randrange(p) for _ in range(2)] + [random.randrange(1, p)]
    g2 = [random.randrange(p) for _ in range(2)] + [random.randrange(1, p)]
    P1 = [random.randrange(p) for _ in range(3)]
    P2 = [random.randrange(p) for _ in range(3)]
    ga1, ga2 = 1, 2
    v1 = polmul(g1, m_of([D[i] for i in S1]))
    v2 = polmul(g2, m_of([D[i] for i in S2]))
    num = padd(padd(v1, v2, s=-1), padd(P1, P2, s=-1))
    cinv = pow((ga1 - ga2) % p, p - 2, p)
    R1 = [(x * cinv) % p for x in num]
    # require deg R1 = 9 (else degenerate)
    dR1 = max((i for i in range(len(R1)) if R1[i] % p), default=-1)
    if dR1 != 9:
        deg_killed += 1
        continue
    R0 = padd(padd(v1, P1), [(-(ga1) * x) % p for x in R1])
    u0 = tuple(poleval(R0, x) for x in D)
    u1 = tuple(poleval(R1, x) for x in D)
    b1 = is_bad_faithful(u0, u1, ga1)
    b2 = is_bad_faithful(u0, u1, ga2)
    if b1 and b2:
        exist += 1
        # check attachment: max (<k)-agreement of R1 with quadratics on the
        # union S1∪S2 -- does the construction create big agreement sets?
        # quick check: agreement of R1 restricted to each witness's points
        maxagr = 0
        for S in (S1, S2):
            for tri in itertools.combinations(S, 3):
                # quadratic through R1 at tri; count agreement on D
                tp = [D[i] for i in tri]
                tv = [u1[i] for i in tri]
                cnt = 0
                for i in range(n):
                    # eval quadratic interpolant at D[i]
                    x = D[i]
                    tot = 0
                    for a_, (xa, ya) in enumerate(zip(tp, tv)):
                        nm, dn = 1, 1
                        for b_, (xb, _) in enumerate(zip(tp, tv)):
                            if a_ == b_:
                                continue
                            nm = nm * ((x - xb) % p) % p
                            dn = dn * ((xa - xb) % p) % p
                        tot = (tot + ya * nm * pow(dn, p - 2, p)) % p
                    if tot == u1[i]:
                        cnt += 1
                maxagr = max(maxagr, cnt)
        if maxagr >= 6:
            attach_created += 1
    else:
        joint_killed += 1
print(f"constructions: {TR}; deg-degenerate: {deg_killed}; "
      f"both-bad (pool pair EXISTS): {exist}; killed: {joint_killed}")
print(f"of existing pairs, constructions with R1-agreement >= 6 "
      f"(secretly attached): {attach_created}")

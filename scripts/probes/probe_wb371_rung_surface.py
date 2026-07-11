#!/usr/bin/env python3
"""
The rung-surface probe: does the division-identity/pair-collapse machinery
bite at the d=2 level-1 rung (p=12289, n=16, k=3, agreement threshold 7)?

The obligation (SubCeilingInteriorCeiling at the instance): for ALL stacks,
#bad gamma at agreement >= 7 is <= 31.  Probed truth: max 16 (the antipodal
pencil (X^8, X^9)).  Per-witness subset counting caps at 52 > 31 (their no-go).

My surface: every row at slack w=9 has WB reps (kernel dim >= 6); the division
identity per witness still holds per rep.  For POLYNOMIAL rows (deg <= 11),
the identity is Phi = R0 + gamma*R1 - p = g*m_S with deg g <= deg Phi - |S|.

Tests at (12289, 16, k=3):
 (1) Reproduce the pencil's 16 bad scalars (faithful mcaEvent at agreement 7).
 (2) For each bad gamma of the pencil, extract witnesses and check the
     identity structure: what are the g's, the S's, the pairwise S-overlaps?
 (3) THE PAIR QUESTION: for bad pairs (gamma, gamma'), is there a structural
     relation (telescope-like) visible in (S, g, p) data?
 (4) Adversarial: search for stacks with MORE than 16 bad (toward 31);
     structured families: (X^a, X^b) monomials, pencil + perturbations,
     two-orbit alignments.  If nothing beats 16, the conjecture
     'bad <= 16 = n' sharpens the obligation (and my surface must prove it).
"""
import itertools, random

p, n, k = 12289, 16, 3
need = 7   # agreement threshold (radius < 5/8)

# smooth domain mu_16 in F_p: generator of the full group, then power
def mu_n():
    # find multiplicative generator of F_p^*
    fact = [2, 3]  # p-1 = 12288 = 2^12 * 3
    for g in range(2, 200):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fact):
            h = pow(g, (p - 1) // n, p)
            return sorted(pow(h, j, p) for j in range(n))
    raise RuntimeError

D = mu_n()
idx = {x: i for i, x in enumerate(D)}

def lagrange_fits(points, vals, deg):
    """is there a poly of degree <= deg through the given (points, vals)?
       check: interpolate on deg+1 points, verify the rest."""
    pts = list(zip(points, vals))
    base = pts[:deg + 1]
    # Lagrange evaluation at the remaining points
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
    return all(evalL(x) == y % p for x, y in pts[deg + 1:])

SUBS7 = list(itertools.combinations(range(n), need))   # C(16,7) = 11440

def explainable_on(u0, u1, g, S):
    pts = [D[i] for i in S]
    vals = [(u0[i] + g * u1[i]) % p for i in S]
    return lagrange_fits(pts, vals, k - 1)

def joint_on(u0, u1, S):
    pts = [D[i] for i in S]
    return (lagrange_fits(pts, [u0[i] % p for i in S], k - 1) and
            lagrange_fits(pts, [u1[i] % p for i in S], k - 1))

def bad_set(u0, u1, gammas=None):
    out = []
    for g in (gammas if gammas is not None else range_sample()):
        found = False
        for S in SUBS7:
            if explainable_on(u0, u1, g, S) and not joint_on(u0, u1, S):
                found = True
                break
        if found:
            out.append(g)
    return out

def range_sample():
    # checking all p=12289 gammas x 11440 subsets is too slow in python;
    # use the structural candidates: the inversion orbit -1/x for x in D,
    # plus a random sample
    cands = set()
    for x in D:
        cands.add((-pow(x, p - 2, p)) % p)
    cands.update(random.sample(range(p), 200))
    return sorted(cands)

random.seed(101)
# (1) the pencil
u0 = tuple(pow(x, 8, p) for x in D)
u1 = tuple(pow(x, 9, p) for x in D)
orbit = sorted((-pow(x, p - 2, p)) % p for x in D)
bad = bad_set(u0, u1, gammas=orbit + random.sample(range(p), 60))
print(f"pencil (X^8, X^9): #bad found = {len(bad)} (orbit hits: "
      f"{sum(1 for g in bad if g in orbit)}/16)")

# (2) witness anatomy for two bad gammas
for g in bad[:2]:
    wits = []
    for S in SUBS7:
        if explainable_on(u0, u1, g, S) and not joint_on(u0, u1, S):
            wits.append(S)
            if len(wits) >= 4:
                break
    print(f"  gamma={g}: first witnesses {wits[:3]}")
    if wits:
        Spts = [sorted(D[i] for i in wits[0])]
        print(f"    witness points: {Spts}")

# (4) adversarial: monomial sweeps + perturbed pencils
best = (len(bad), "pencil")
for (a, b) in [(8, 9), (8, 10), (7, 9), (8, 7), (4, 12), (8, 11), (6, 9),
               (5, 8), (8, 13), (12, 13)]:
    v0 = tuple(pow(x, a, p) for x in D)
    v1 = tuple(pow(x, b, p) for x in D)
    bs = bad_set(v0, v1)
    if len(bs) > best[0]:
        best = (len(bs), f"(X^{a},X^{b})")
    print(f"  (X^{a},X^{b}): #bad (sampled) = {len(bs)}")
# perturbed pencil: pencil + small spike
for trial in range(4):
    v0 = list(u0); v1 = list(u1)
    i0 = random.randrange(n)
    v0[i0] = random.randrange(p)
    bs = bad_set(tuple(v0), tuple(v1))
    print(f"  pencil + spike@{i0}: #bad (sampled) = {len(bs)}")
    if len(bs) > best[0]:
        best = (len(bs), f"spiked-pencil")
print(f"\nMAX found: {best}")

#!/usr/bin/env python3
"""
Case-tree exhaustiveness check on the record-22 stack (p=12289).

The planned summation theorem partitions bad scalars as:
  Z  zero-class (g = 0: folded row globally deg<3)
  C1 members of class 1 (witness overlap >= 3 with another scalar,
     assigned to the (A,r) of that overlap)  [per class: <= 16-|A|]
  S  solo (pairwise overlaps <= 2)           [Fisher <= 16]
Verify on the 21/22-record stacks: every bad scalar lands in exactly one
bucket, count buckets, and measure the off-part split of class members
across {other-class frame pts, other-class non-frame pts, free pts} --
the regions of the cross-restriction/collision laws.
"""
import itertools, random
src = open("scripts/probes/probe_wb371_blockladder2.py").read()
ns = {}
exec(src[:src.index("best_per_ns")], ns)
p, n, D, peval = ns['p'], ns['n'], ns['D'], ns['peval']
census_set, solve_linear, pencil_row = ns['census_set'], ns['solve_linear'], ns['pencil_row']
MATS = ns['MATS']
s = 7

def census_with_witnesses(u0, u1):
    bad = {}
    for S, M in MATS:
        v0 = [u0[i] for i in S]; v1 = [u1[i] for i in S]
        tb = [sum(M[r][j]*v1[j] for j in range(s)) % p for r in range(4)]
        if not any(tb): continue
        ta = [sum(M[r][j]*v0[j] for j in range(s)) % p for r in range(4)]
        j = next(t for t in range(4) if tb[t])
        gam = (-ta[j]) * pow(tb[j], p-2, p) % p
        if all((ta[t] + gam*tb[t]) % p == 0 for t in range(4)):
            bad.setdefault(gam, []).append(set(S))
    return bad

# rebuild the ns=2 record stack (seed from ladder2 trial 0)
rng = random.Random(7000 + 97*0 + 2)
gams = rng.sample(range(2, p), 2)
b1pts = rng.sample(range(0, 6), 4); b2pts = rng.sample(range(6, 12), 4)
rows = []
for j, g in enumerate(gams):
    for i in b1pts[2*j:2*j+2]: rows.append(pencil_row(0, 6, D[i], g))
    for i in b2pts[2*j:2*j+2]: rows.append(pencil_row(3, 9, D[i], g))
sol = solve_linear(rows, 18, rng)
q1, q2, r1, r2 = sol[0:3], sol[3:6], sol[6:9], sol[9:12]
q3, r3 = sol[12:15], sol[15:18]
u0, u1 = [0]*n, [0]*n
for i in range(6): u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
for i in range(6, 12): u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
for i in (12, 13, 14): u1[i] = peval(q3, D[i]); u0[i] = peval(r3, D[i])
ga, gb = rng.randrange(1, p), rng.randrange(1, p)
x = D[15]
rhs1 = (peval(r1, x) + ga*peval(q1, x)) % p
rhs2 = (peval(r2, x) + gb*peval(q2, x)) % p
R1x = (rhs1 - rhs2) * pow((ga - gb) % p, p-2, p) % p
u1[15] = R1x; u0[15] = (rhs1 - ga*R1x) % p

bad = census_with_witnesses(u0, u1)
print(f"total bad: {len(bad)}")
gammas = list(bad)
# pick one minimal witness per scalar (first found)
wit = {g: min(bad[g], key=len) for g in gammas}
# pairwise overlaps -> solo vs paired
paired = {}
for g in gammas:
    partners = [g2 for g2 in gammas if g2 != g and len(wit[g] & wit[g2]) >= 3]
    paired[g] = partners
solo = [g for g in gammas if not paired[g]]
classes = {}
for g in gammas:
    if paired[g]:
        # class key = frozenset of the overlap-extended component (crude)
        comp = frozenset([g] + paired[g])
        classes.setdefault(comp, set()).add(g)
# merge overlapping components
merged = []
for comp, mems in classes.items():
    placed = False
    for mset in merged:
        if mset & mems:
            mset |= mems; placed = True; break
    if not placed:
        merged.append(set(mems))
print(f"solo: {len(solo)}; classes: {[len(m) for m in merged]}")
print(f"sum check: {len(solo) + sum(len(m) for m in merged)} == {len(bad)}")
# off-part split for the biggest class (its A = most-common 6-point core)
if merged:
    big = max(merged, key=len)
    cores = {}
    for g in big:
        for g2 in big:
            if g2 != g and len(wit[g] & wit[g2]) >= 3:
                core = frozenset(wit[g] & wit[g2])
                cores[core] = cores.get(core, 0) + 1
    A = set(max(cores, key=lambda c: (cores[c], len(c))))
    regions = {"A2frame": 0, "A2other": 0, "free": 0}
    A1, A2 = set(range(6)), set(range(6, 12))
    other = A2 if A <= A1 or len(A & A1) >= 3 else A1
    for g in big:
        off = wit[g] - A
        for i in off:
            if i in other:
                regions["A2frame"] += 1   # frame pts (R0 = r_other on all of A_other here)
            elif i in A1 | A2:
                regions["A2other"] += 1
            else:
                regions["free"] += 1
    print(f"biggest class |A∩found|={len(A)}, size {len(big)}, "
          f"off-part region counts: {regions}")

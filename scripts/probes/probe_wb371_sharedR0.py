#!/usr/bin/env python3
"""
Does the shared-R0 coupling bound the total below Sum(n-|A|)? (p=12289)

Critical test of the residual's cap choice. Three DISJOINT size-5
agreement sets A1={0-4},A2={5-9},A3={10-14} CAN coexist (R1 = q_i on A_i
is consistent, deg<=15). Per-class cap n-|A| = 11, so Sum caps = 33 > 31.
If each class could independently realize ~11 attached scalars, total
> 31 and the obligation is REFUTED. But R0 is SHARED: the candidate map
f_i = -(R0-r_i)/(R1-q_i) for class i; attached gamma <-> pairs of off-pts
with equal f_i. Setting R0 to create f_1-collisions also moves f_2,f_3.

This probe HILL-CLIMBS R0's 16 values (R1 fixed by 3 quadratics + 1 free
pt) to MAXIMIZE total bad scalars, testing whether the shared-R0 coupling
caps the total. If max stays ~22, the n-|A| cap is loose and the bound
comes from shared-R0 (=> residual needs the attachment count, not caps).
If max > 31, obligation refuted.
"""
import itertools, random
src = open("scripts/probes/probe_wb371_refute31.py").read()
ns = {}
exec(src[:src.index("# class-set patterns")], ns)
p, n, D, peval, interp, census = ns['p'], ns['n'], ns['D'], ns['peval'], ns['interp'], ns['census']

A = [list(range(0,5)), list(range(5,10)), list(range(10,15))]
free_pt = 15
rng = random.Random(77)

def build_R1():
    # R1 = q_i (random quadratic) on A_i, random on pt 15
    u1 = [0]*n
    for b in A:
        q = [rng.randrange(p) for _ in range(3)]
        for i in b: u1[i] = peval(q, D[i])
    u1[free_pt] = rng.randrange(p)
    return u1

best_overall = 0
for restart in range(6):
    u1 = build_R1()
    u0 = [rng.randrange(p) for _ in range(n)]
    cur = census(u0, u1)
    improved = True; rounds = 0
    while improved and rounds < 5:
        improved = False; rounds += 1
        order = list(range(n)); rng.shuffle(order)
        for i in order:
            old = u0[i]
            for _ in range(12):
                u0[i] = rng.randrange(p)
                c = census(u0, u1)
                if c > cur:
                    cur = c; old = u0[i]; improved = True; break
                u0[i] = old
            # also try perturbing u1 at free pt and A-points (changes quadratics)
        # occasionally re-randomize a whole class quadratic on u1
    if cur > best_overall:
        best_overall = cur
    print(f"restart {restart}: R0-hillclimb max = {cur}")
print(f"SHARED-R0 RESULT: max total = {best_overall} over 3 disjoint size-5 "
      f"classes (Sum caps n-|A| = 33); obligation 31; "
      f"{'REFUTED' if best_overall > 31 else 'holds => n-|A| cap loose, '
        'shared-R0 coupling binds'}")

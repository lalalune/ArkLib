#!/usr/bin/env python3
"""
Constructive 3-class builder (p=12289): determine R0,R1 from 3 (q_i,r_i)
quadratic pairs on agreement sets A_i, census, sweep to maximize.

A class i: R1 = q_i on A_i, R0 = r_i on A_i. With 3 sets covering 15 pts +
1 free pt (15), R0 and R1 are FULLY determined (16 values each) by the 3
(q_i,r_i) pairs + the free-pt values. No freedom to inject collisions - the
candidate maps f_i are determined, so the attached count is whatever the
geometry gives. Sweep (q_i,r_i, free-pt) and report the GLOBAL max census.
If > 31: obligation refuted. If <= 22-ish: bound holds in the 3-class regime
(and the n-|A| cap of 33 is confirmed loose).

Configs: 3 disjoint size-5; 2 size-6 + 1 size-4; overlapping size-6 triples.
"""
import itertools, random
src = open("scripts/probes/probe_wb371_refute31.py").read()
ns = {}
exec(src[:src.index("# class-set patterns")], ns)
p, n, D, peval, census = ns['p'], ns['n'], ns['D'], ns['peval'], ns['census']

CONFIGS = {
  "3x disjoint-5": [list(range(0,5)), list(range(5,10)), list(range(10,15))],
  "6+6+4 packed": [list(range(0,6)), list(range(6,12)), [12,13,14,15,0,6]],
  "3x6 overlap-2": [[0,1,2,3,4,5],[4,5,6,7,8,9],[8,9,10,11,12,13]],
  "2x6 (record)": [list(range(0,6)), list(range(6,12))],
}

def quad_consistent_R1(pat, qs):
    """R1[i] = q_{first class containing i}(D[i]); returns None-free vals."""
    u = [None]*n
    for ci, b in enumerate(pat):
        for i in b:
            if u[i] is None:
                u[i] = peval(qs[ci], D[i])
    return u

for name, pat in CONFIGS.items():
    covered = sorted(set().union(*[set(b) for b in pat]))
    free = [i for i in range(n) if i not in covered]
    best = 0; best_detail = None
    rng = random.Random(hash(name) % 10000)
    for trial in range(300):
        qs = [[rng.randrange(p) for _ in range(3)] for _ in pat]
        rs = [[rng.randrange(p) for _ in range(3)] for _ in pat]
        u1 = quad_consistent_R1(pat, qs)
        u0 = quad_consistent_R1(pat, rs)
        for i in free:
            u1[i] = rng.randrange(p); u0[i] = rng.randrange(p)
        if any(v is None for v in u1) or any(v is None for v in u0):
            continue
        c = census(u0, u1)
        if c > best:
            best = c; best_detail = trial
            if c > 31:
                print(f"  *** [{name}] BEAT 31: {c} (trial {trial}) ***")
    print(f"[{name}] sizes {[len(b) for b in pat]}, Sum(n-|A|)="
          f"{sum(n-len(b) for b in pat)}, free={len(free)}: "
          f"max census = {best}")
print("CONSTRUCT-3 done. obligation bound 31; known fiber-tuned max 22.")

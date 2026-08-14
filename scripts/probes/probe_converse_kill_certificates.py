#!/usr/bin/env python3
"""#357 exactness-converse lane: kill certificates for the generic-branch case tree.

By the trichotomy (WideCircuitTrichotomy.lean) the converse reduces to the GENERIC
branch: balanced Distinct6 triples with all products pairwise distinct mod n and all
pair-sums pairwise distinct (at most one antipodal pair).  In the multiplicity-free
stratum the matching is canonical, and this probe charts the full case tree:

  (a) classify all 66 index-pairs as locally-dead (their single congruence already
      violates Distinct6 / genericity) or live;
  (b) enumerate all perfect matchings using live pairs only;
  (c) for each, search a kill certificate: a small integer combination of the six
      pair-congruences equal to a forbidden form —
        * x_i - x_j = 0      (Distinct6 violation),
        * s_i - s_j = 0      (product collision: not generic),
        * (a_i - b_i = h) twice (two antipodal pairs: sum collision, not generic),
        * exp_x - exp_y = (0 same-sign / h cross-sign)  (12-term multiplicity: not
          multiplicity-free),
      with branching on doubled forms 2v = 0/2v = h (doubling kernel {0,h});
  (d) survivors must be exactly the 12 generic patterns (4 family + 8 second-layer)
      of probe_matching_converse_patterns.py; cross-checked, and each survivor's
      reduced congruence system printed for the Lean forcing lemmas.

Output: per-matching verdict + certificate, machine-checkable; the case-tree sizes
that the Lean transcription will need.
"""
from itertools import combinations
import sys

# symbol order: a1 b1 a2 b2 a3 b3 ;  s_i = a_i + b_i
EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),    # 0,1   e2*m3  [+]
    (1,1,1,0,0,0), (1,1,0,1,0,0),    # 2,3   e2*m1  [-]
    (1,0,0,0,1,1), (0,1,0,0,1,1),    # 4,5   e1*m3  [-]
    (0,0,1,1,1,0), (0,0,1,1,0,1),    # 6,7   e3*m2  [-]
    (1,0,1,1,0,0), (0,1,1,1,0,0),    # 8,9   e1*m2  [+]
    (1,1,0,0,1,0), (1,1,0,0,0,1),    # 10,11 e3*m1  [+]
]
SIGN = [1,1,-1,-1,-1,-1,-1,-1,1,1,1,1]
NAMES = ['a1','b1','a2','b2','a3','b3']

def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vneg(u): return tuple(-x for x in u)
def vzero(u): return all(x==0 for x in u)

def pair_congruence(x, y):
    """matching pair {x,y}: E(x) = E(y) + h with E = exp + (0 if +, h if -).
    same-sign: exp_x - exp_y = h (flag 1); cross-sign: exp_x - exp_y = 0 (flag 0)."""
    vec = vsub(EXPVEC[x], EXPVEC[y])
    flag = 1 if SIGN[x]==SIGN[y] else 0
    return vec, flag

# forbidden target forms (vector, flag, kind)
def unit(i):
    return tuple(1 if k==i else 0 for k in range(6))

TARGETS = []
for i in range(6):
    for j in range(i+1,6):
        TARGETS.append((vsub(unit(i),unit(j)), 0, f'D6:{NAMES[i]}={NAMES[j]}'))
SVEC = [ (1,1,0,0,0,0), (0,0,1,1,0,0), (0,0,0,0,1,1) ]
for i in range(3):
    for j in range(i+1,3):
        TARGETS.append((vsub(SVEC[i],SVEC[j]), 0, f'GEN:s{i+1}=s{j+1}'))
# multiplicity targets: exp_x - exp_y = (0 same-sign, h cross-sign), x != y not matched
MULT = []
for x in range(12):
    for y in range(x+1,12):
        MULT.append((vsub(EXPVEC[x],EXPVEC[y]), 0 if SIGN[x]==SIGN[y] else 1,
                     f'MULT:{x},{y}'))
ANTIP = [(vsub(unit(2*i),unit(2*i+1)), 1, f'ANTIP:{i+1}') for i in range(3)]

def lattice_solve(rows, flags, target_vec, target_flag, maxc=2):
    """search small integer lambda with sum l_i rows_i = target_vec and
    sum l_i flags_i = target_flag (mod 2). returns lambda or None."""
    k = len(rows)
    rng = range(-maxc, maxc+1)
    # meet in the middle over first half/second half for speed
    from itertools import product
    half = k//2
    first = {}
    for lam1 in product(rng, repeat=half):
        v = tuple(sum(l*rows[i][t] for i,l in enumerate(lam1)) for t in range(6))
        f = sum(l*flags[i] for i,l in enumerate(lam1)) % 2
        first.setdefault((v,f), lam1)
    for lam2 in product(rng, repeat=k-half):
        v2 = tuple(sum(l*rows[half+i][t] for i,l in enumerate(lam2)) for t in range(6))
        f2 = sum(l*flags[half+i] for i,l in enumerate(lam2)) % 2
        need_v = vsub(target_vec, v2)
        need_f = (target_flag - f2) % 2
        if (need_v, need_f) in first:
            return first[(need_v,need_f)] + lam2
    return None

def analyze(matching, extra_rows=(), extra_flags=(), depth=0, antip_seen=()):
    """returns (verdict, certificate). verdict in {'KILL','FEASIBLE'}"""
    rows, flags = [], []
    for (x,y) in matching:
        v,f = pair_congruence(x,y)
        rows.append(v); flags.append(f)
    rows += list(extra_rows); flags += list(extra_flags)
    # direct kills
    for tv, tf, kind in TARGETS:
        for sgn in (1,-1):
            lam = lattice_solve(rows, flags, tuple(sgn*t for t in tv), tf)
            if lam is not None:
                return ('KILL', (kind, lam))
    # multiplicity kills: only x,y NOT matched together
    mset = {frozenset(p) for p in matching}
    for tv, tf, kind in MULT:
        x,y = map(int, kind.split(':')[1].split(','))
        if frozenset((x,y)) in mset: continue
        for sgn in (1,-1):
            lam = lattice_solve(rows, flags, tuple(sgn*t for t in tv), tf)
            if lam is not None:
                return ('KILL', (kind, lam))
    # double-antipodal kill: two distinct ANTIP derivable
    found_antip = list(antip_seen)
    for tv, tf, kind in ANTIP:
        if kind in found_antip: continue
        for sgn in (1,-1):
            lam = lattice_solve(rows, flags, tuple(sgn*t for t in tv), tf)
            if lam is not None:
                found_antip.append(kind)
                break
    if len(found_antip) >= 2:
        return ('KILL', ('TWO-ANTIPODAL:'+','.join(found_antip), None))
    # branching on doubled forms: 2*(x_i - x_j) = 0 derivable but x_i - x_j = 0/h not yet
    if depth < 2:
        for i in range(6):
            for j in range(i+1,6):
                tv = vsub(unit(i),unit(j))
                tv2 = tuple(2*t for t in tv)
                for tf2 in (0,):
                    lam = lattice_solve(rows, flags, tv2, tf2)
                    if lam is None: continue
                    # branch: x_i - x_j = 0 (D6 kill) or = h
                    sub = analyze(matching, list(extra_rows)+[tv],
                                  list(extra_flags)+[1], depth+1, found_antip)
                    if sub[0] == 'KILL':
                        return ('KILL', (f'BRANCH2({NAMES[i]}-{NAMES[j]})', sub[1]))
                    return ('FEASIBLE', f'branch-survivor({NAMES[i]}-{NAMES[j]})')
    return ('FEASIBLE', None)

# local pair classification
local_dead = set()
live_pairs = []
for x in range(12):
    for y in range(x+1,12):
        v,f = pair_congruence(x,y)
        dead = False
        for tv, tf, kind in TARGETS:
            if (v==tv and f==tf) or (v==vneg(tv) and f==tf):
                dead = True; break
        if dead: local_dead.add((x,y))
        else: live_pairs.append((x,y))
print(f"local: {len(local_dead)} dead pairs, {len(live_pairs)} live pairs")

# enumerate perfect matchings using live pairs only
def matchings(elems, acc, out):
    if not elems:
        out.append(tuple(acc)); return
    x = elems[0]
    for y in elems[1:]:
        if (min(x,y),max(x,y)) in live_set:
            matchings([e for e in elems[1:] if e != y], acc+[(x,y)], out)

live_set = set(live_pairs)
all_m = []
matchings(list(range(12)), [], all_m)
print(f"perfect matchings on live pairs: {len(all_m)}")

verdicts = {}
kills = {}
feasible = []
for M in all_m:
    v, cert = analyze(M)
    verdicts[M] = (v, cert)
    if v == 'KILL':
        kind = cert[0] if isinstance(cert, tuple) else cert
        kinds = kind if isinstance(kind,str) else str(kind)
        kills.setdefault(kinds.split(':')[0], []).append(M)
    else:
        feasible.append(M)

print(f"\nkill summary:")
for k, v in sorted(kills.items()):
    print(f"  {k}: {len(v)}")
print(f"FEASIBLE: {len(feasible)}")

# the 12 expected generic patterns from the pattern probe
EXPECTED = [
    "((0, 1), (2, 3), (4, 6), (5, 7), (8, 10), (9, 11))",
    "((0, 1), (2, 3), (4, 7), (5, 6), (8, 11), (9, 10))",
    "((0, 8), (1, 9), (2, 4), (3, 5), (6, 7), (10, 11))",
    "((0, 8), (1, 10), (2, 7), (3, 5), (4, 6), (9, 11))",
    "((0, 8), (1, 11), (2, 6), (3, 5), (4, 7), (9, 10))",
    "((0, 9), (1, 10), (2, 7), (3, 4), (5, 6), (8, 11))",
    "((0, 9), (1, 11), (2, 6), (3, 4), (5, 7), (8, 10))",
    "((0, 10), (1, 8), (2, 5), (3, 7), (4, 6), (9, 11))",
    "((0, 10), (1, 9), (2, 4), (3, 7), (5, 6), (8, 11))",
    "((0, 10), (1, 11), (2, 6), (3, 7), (4, 5), (8, 9))",
    "((0, 11), (1, 8), (2, 5), (3, 6), (4, 7), (9, 10))",
    "((0, 11), (1, 9), (2, 4), (3, 6), (5, 7), (8, 10))",
]
fset = {str(tuple(sorted(tuple(sorted(p)) for p in M))) for M in feasible}
eset = set(EXPECTED)
print(f"\nfeasible == expected 12 generic patterns: {fset == eset}")
if fset != eset:
    print("  extra feasible (need kills or are new patterns!):")
    for M in sorted(fset - eset): print("   ", M)
    print("  expected but killed (BUG in kill search!):")
    for M in sorted(eset - fset): print("   ", M)

# print the feasible systems for the Lean forcing lemmas
print("\n--- feasible systems (congruences, RHS h-flag) ---")
def fmt(vec, flag):
    terms=[]
    for c,nm in zip(vec,NAMES):
        if c==0: continue
        terms.append(('+' if c>0 else '-') + (nm if abs(c)==1 else f'{abs(c)}{nm}'))
    return ''.join(terms).lstrip('+') + (' = h' if flag else ' = 0')
for M in feasible:
    key = tuple(sorted(tuple(sorted(p)) for p in M))
    sys_ = set()
    for (x,y) in M:
        v,f = pair_congruence(x,y)
        sys_.add(min((v,f),(vneg(v),f)))
    print(f"M{key}:")
    for v,f in sorted(sys_): print("   ", fmt(v,f))
print("DONE")

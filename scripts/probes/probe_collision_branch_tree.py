#!/usr/bin/env python3
"""#357 converse increment 4: the COLLISION branch — multiplicity profiles in the
generic stratum.

A balanced Distinct6 config that is NOT multiplicity-free has coincidences among the
12 shifted values. Balance pairs each size-2 fiber with a size-2 antipodal fiber, so
the structures are built from "quartets" (x,y | z,w): E(x)=E(y), E(z)=E(w)=E(x)+h,
plus a perfect antipodal matching of the remaining singles. Profiles measured at
n=16/32: (2,2,1^8) one quartet, (2^4,1^4) two, (2^6) three.

This probe enumerates all quartet choices + singles-matchings in the GENERIC branch
(all three antipodal conditions are kills, products pairwise distinct), searches kill
certificates exactly as the matching probes, and classifies survivors: every survivor
must derive a chord system (+ which) or a second-layer system (+ which) — i.e. the
collision stratum introduces NO new families. The survivor systems + certs are the
blueprint for the Lean collision branch.

NOTE: in the generic branch the antipodal-pair hypotheses are NOT available as kills
(no pair is assumed antipodal) — but a config with an antipodal pair lands in the
chord branch, so here we may also flag ANTIP-derivations as 'chord-side' outcomes
rather than kills. We report both readings.
"""
from itertools import product, combinations

EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),
    (1,1,1,0,0,0), (1,1,0,1,0,0),
    (1,0,0,0,1,1), (0,1,0,0,1,1),
    (0,0,1,1,1,0), (0,0,1,1,0,1),
    (1,0,1,1,0,0), (0,1,1,1,0,0),
    (1,1,0,0,1,0), (1,1,0,0,0,1),
]
SHIFT = [0,0,1,1,1,1,1,1,0,0,0,0]
def esv(i): return tuple(list(EXPVEC[i]) + [SHIFT[i]])
NAMES = ['a1','b1','a2','b2','a3','b3','h']
def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vadd(u,v): return tuple(x+y for x,y in zip(u,v))
def vneg(u): return tuple(-x for x in u)
def smul(c,u): return tuple(c*x for x in u)
ZERO7 = tuple([0]*7)
def unit7(i): return tuple(1 if k==i else 0 for k in range(7))
EH = unit7(6)

def coin_diff(x, y):   # E(x) = E(y)
    return vsub(esv(x), esv(y))
def pair_diff(x, v):   # E(v) = E(x) + h
    return vsub(vsub(esv(v), esv(x)), EH)

KILLS = []
PAIRS6 = [(i,j) for i in range(6) for j in range(i+1,6)]
for (i,j) in PAIRS6:
    KILLS.append(('D6', (i,j), vsub(unit7(i), unit7(j))))
for (i,j) in [(0,1),(0,2),(1,2)]:
    sv_i = vadd(unit7(2*i), unit7(2*i+1)); sv_j = vadd(unit7(2*j), unit7(2*j+1))
    KILLS.append(('GEN', (i,j), vsub(sv_i, sv_j)))
ANTIPS = [('ANTIP', i, vsub(vsub(unit7(2*i+1), unit7(2*i)), EH)) for i in range(3)]

def solve(rows, target, maxc=2):
    k = len(rows)
    rng = range(-maxc, maxc+1)
    half = k//2
    first = {}
    for lam1 in product(rng, repeat=half):
        v = ZERO7
        for i,l in enumerate(lam1):
            if l: v = vadd(v, smul(l, rows[i]))
        first.setdefault(v, lam1)
    for lam2 in product(rng, repeat=k-half):
        v2 = ZERO7
        for i,l in enumerate(lam2):
            if l: v2 = vadd(v2, smul(l, rows[half+i]))
        need = vsub(target, v2)
        body = need[:6]
        for v1, lam1 in first.items():
            if v1[:6] != body: continue
            dh = need[6] - v1[6]
            if dh % 2 == 0:
                return (lam1 + lam2, dh//2)
    return None

def kill_or_route(rows, depth=0):
    """returns ('KILL', kind) / ('CHORD', i) / None"""
    for kind, payload, tv in KILLS:
        for sgn in (1,-1):
            if solve(rows, tuple(sgn*t for t in tv)) is not None:
                return ('KILL', f'{kind}:{payload}')
    for kind, i, tv in ANTIPS:
        if solve(rows, tv) is not None:
            return ('CHORD', i+1)   # an antipodal pair is derivable: chord-side
    if depth < 1:
        for i in range(6):
            for j in range(i+1, 6):
                tv2 = smul(2, vsub(unit7(i), unit7(j)))
                if solve(rows, tv2) is None: continue
                extra = vsub(vsub(unit7(i), unit7(j)), EH)
                sub = kill_or_route(rows + [extra], depth+1)
                if sub is not None and sub[0] == 'KILL':
                    return ('KILL', f'BRANCH({NAMES[i]}-{NAMES[j]})->{sub[1]}')
                # h-arm gives x_i - x_j = h: if (i,j) is a pair (a_k, b_k) that IS
                # an antipodal derivation -> chord-side
                if (i,j) in [(0,1),(2,3),(4,5)] and sub is None:
                    return None
    return None

# second-layer system targets (from the no-antipodal probe survivors)
def parse_goal(g):
    NM = {'a1':0,'b1':1,'a2':2,'b2':3,'a3':4,'b3':5}
    lhs, rhs = g.split('=')
    v = ZERO7
    for t in lhs.strip().split('+'):
        v = vadd(v, unit7(NM[t.strip()]))
    for t in rhs.strip().split('+'):
        t = t.strip()
        if t == 'h': v = vsub(v, EH)
        else: v = vsub(v, unit7(NM[t]))
    return v
SYS = [
    ["b2+b3 = a1+b1+h", "a3+b3 = a1+b2+h", "a2+b2 = a1+b3+h"],
    ["b2+a3 = a1+b1+h", "a3+b3 = a1+b2+h", "a2+b2 = a1+a3+h"],
    ["b2+b3 = a1+b1+h", "a3+b3 = b1+b2+h", "a2+b2 = b1+b3+h"],
    ["b2+a3 = a1+b1+h", "a3+b3 = b1+b2+h", "a2+b2 = b1+a3+h"],
    ["a2+b3 = a1+b1+h", "a3+b3 = a1+a2+h", "a2+b2 = a1+b3+h"],
    ["a2+b3 = a1+b1+h", "a3+b3 = b1+a2+h", "a2+b2 = b1+b3+h"],
    ["a2+a3 = a1+b1+h", "a3+b3 = a1+a2+h", "a2+b2 = a1+a3+h"],
    ["a2+a3 = a1+b1+h", "a3+b3 = b1+a2+h", "a2+b2 = b1+a3+h"],
]
SYSV = [[parse_goal(g) for g in s] for s in SYS]

def derives_secondlayer(rows):
    for sidx, tvs in enumerate(SYSV):
        if all(solve(rows, tv) is not None for tv in tvs):
            return sidx
    return None

def pairings(elems):
    if not elems: yield []
    else:
        x = elems[0]
        for y in elems[1:]:
            rest = [e for e in elems[1:] if e != y]
            for p in pairings(rest):
                yield [(x,y)] + p

# one-quartet structures: choose {x,y} same... any pair (the congruence handles sign),
# {z,w} disjoint, + matching of the 8 remaining singles
results = {'KILL':0, 'CHORD':0, 'SECOND':0, 'OPEN':[]}
idx = list(range(12))
count = 0
for xy in combinations(idx, 2):
    for zw in combinations([i for i in idx if i not in xy], 2):
        base = [coin_diff(*xy), coin_diff(*zw), pair_diff(xy[0], zw[0])]
        # quick prefix check
        r = kill_or_route(base)
        if r is not None:
            count_inc = 1
            count += 1
            if r[0] == 'KILL': results['KILL'] += 1
            else: results['CHORD'] += 1
            continue
        rest = [i for i in idx if i not in xy and i not in zw]
        for P in pairings(rest):
            count += 1
            rows = base + [pair_diff(x, v) for (x,v) in P]
            r = kill_or_route(rows)
            if r is not None:
                if r[0] == 'KILL': results['KILL'] += 1
                else: results['CHORD'] += 1
                continue
            s = derives_secondlayer(rows)
            if s is not None:
                results['SECOND'] += 1
            else:
                results['OPEN'].append((xy, zw, tuple(P)))
print(f"one-quartet structures scanned: {count}")
print(f"  killed: {results['KILL']}, chord-side: {results['CHORD']}, "
      f"second-layer: {results['SECOND']}, OPEN: {len(results['OPEN'])}")
for o in results['OPEN'][:20]:
    print("  OPEN:", o)
print("DONE")

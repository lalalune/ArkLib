#!/usr/bin/env python3
"""#357 converse increment 4b: the multi-quartet collision profiles (2^4,1^4), (2^6).

Completes probe_collision_branch_tree.py: two- and three-quartet structures in the
generic branch. Verdict per structure: KILL / chord-side (antipodal derivable) /
second-layer / OPEN. Expected from the classification: zero OPEN.
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
def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vadd(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(c,u): return tuple(c*x for x in u)
ZERO7 = tuple([0]*7)
def unit7(i): return tuple(1 if k==i else 0 for k in range(7))
EH = unit7(6)
NAMES = ['a1','b1','a2','b2','a3','b3','h']

def coin_diff(x, y): return vsub(esv(x), esv(y))
def pair_diff(x, v): return vsub(vsub(esv(v), esv(x)), EH)

KILLS = []
for i in range(6):
    for j in range(i+1,6):
        KILLS.append(vsub(unit7(i), unit7(j)))
for (i,j) in [(0,1),(0,2),(1,2)]:
    sv_i = vadd(unit7(2*i), unit7(2*i+1)); sv_j = vadd(unit7(2*j), unit7(2*j+1))
    KILLS.append(vsub(sv_i, sv_j))
ANTIPS = [vsub(vsub(unit7(2*i+1), unit7(2*i)), EH) for i in range(3)]

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

def verdict(rows, depth=0):
    for tv in KILLS:
        if solve(rows, tv) is not None or solve(rows, smul(-1, tv)) is not None:
            return 'KILL'
    for tv in ANTIPS:
        if solve(rows, tv) is not None:
            return 'CHORD'
    if depth < 1:
        for i in range(6):
            for j in range(i+1, 6):
                tv2 = smul(2, vsub(unit7(i), unit7(j)))
                if solve(rows, tv2) is None: continue
                extra = vsub(vsub(unit7(i), unit7(j)), EH)
                sub = verdict(rows + [extra], depth+1)
                if sub == 'KILL':
                    return 'KILL'
    return None

def parse_goal(g):
    NM = {'a1':0,'b1':1,'a2':2,'b2':3,'a3':4,'b3':5}
    lhs, rhs = g.split('=')
    v = ZERO7
    for t in lhs.strip().split('+'): v = vadd(v, unit7(NM[t.strip()]))
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
def second(rows):
    for tvs in SYSV:
        if all(solve(rows, tv) is not None for tv in tvs):
            return True
    return False

def quartet_rows(xy, zw):
    return [coin_diff(*xy), coin_diff(*zw), pair_diff(xy[0], zw[0])]

def pairings(elems):
    if not elems: yield []
    else:
        x = elems[0]
        for y in elems[1:]:
            rest = [e for e in elems[1:] if e != y]
            for p in pairings(rest):
                yield [(x,y)] + p

idx = list(range(12))
# TWO quartets + 4 singles
res2 = {'KILL':0,'CHORD':0,'SECOND':0,'OPEN':[]}
n2 = 0
for q1xy in combinations(idx, 2):
    rest1 = [i for i in idx if i not in q1xy]
    for q1zw in combinations(rest1, 2):
        base1 = quartet_rows(q1xy, q1zw)
        if verdict(base1) == 'KILL':
            continue  # all extensions die; count coarsely below
        rest2 = [i for i in rest1 if i not in q1zw]
        for q2xy in combinations(rest2, 2):
            if q2xy[0] != rest2[0]: break  # canonical: first free index anchors q2
            rest3 = [i for i in rest2 if i not in q2xy]
            for q2zw in combinations(rest3, 2):
                rows = base1 + quartet_rows(q2xy, q2zw)
                n2 += 1
                v = verdict(rows)
                if v == 'KILL': res2['KILL'] += 1; continue
                if v == 'CHORD': res2['CHORD'] += 1; continue
                rest4 = [i for i in rest3 if i not in q2zw]
                allk = True; anyopen = False
                for P in pairings(rest4):
                    rows2 = rows + [pair_diff(x, y) for (x,y) in P]
                    v2 = verdict(rows2)
                    if v2 == 'KILL': continue
                    if v2 == 'CHORD': res2['CHORD'] += 1; allk = False; continue
                    if second(rows2): res2['SECOND'] += 1; allk = False
                    else:
                        res2['OPEN'].append((q1xy,q1zw,q2xy,q2zw,tuple(P)))
                        anyopen = True; allk = False
                if allk: res2['KILL'] += 1
print(f"two-quartet structures: {n2}; verdicts {dict((k, len(v) if isinstance(v,list) else v) for k,v in res2.items())}")
for o in res2['OPEN'][:10]: print("  OPEN:", o)
print("DONE")

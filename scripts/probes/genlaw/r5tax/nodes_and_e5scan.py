#!/usr/bin/env python3
"""(1) e5 census over ALL parity-pure (O,mask) configs (not just live) + death-reason
census for e5 >= 3 configs.  (2) The 70-row node table for DERIVED-99512.md."""
import itertools, collections, json
from math import comb

S, N, A, R, B = 32, 64, 16, 5, 14
TYPES = {('','P'):'np', ('','O'):'no', ('O','P'):'a', ('O','O'):'q',
         ('P','P'):'p5', ('OP','P'):'f3'}

def profile(O, m, Oset):
    a = [O[0]] + [O[i] + S * ((m >> (i - 1)) & 1) for i in range(1, R)]
    slots = collections.Counter()
    prods = []
    for i in range(R):
        for j in range(i + 1, R):
            sl = (a[i] + a[j]) % N
            prods.append(sl); slots[sl] += 1
    for o in O: slots[(2 * o) % N] += 1
    slots[48] += 1
    e5 = 0
    for x in range(10):
        for y in range(x + 1, 10):
            if (prods[x] - prods[y]) % N == S or (prods[y] - prods[x]) % N == S:
                e5 += 1
    # liveness
    reason = None; h = v = 0
    for c in range(A):
        d = slots[2 * c] - slots[2 * c + S]
        if abs(d) >= 2: reason = reason or 'axis|D|>=2'
        elif d == 1 and (c + A) in O: reason = reason or 'forcedB-in-O'
        elif d == -1 and c in Oset: reason = reason or 'forcedB-in-O'
        elif d != 0: h += 1
        elif d == 0 and (c not in O) and ((c + A) not in O) and c != 8 or \
             (d == 0 and c == 8 and slots[16] + slots[48] == 1 and False):
            pass
    # recompute cleanly
    h = v = 0; reason = None
    for c in range(A):
        d = slots[2 * c] - slots[2 * c + S]
        has_o = (c in Oset) or ((c + A) in Oset)
        if d == 0:
            if not has_o and (slots[2*c] + slots[2*c+S] == 0 or True):
                # free only if axis has no O fiber; occupancy irrelevant if balanced
                v += 1
        elif d == 1:
            if (c + A) in Oset: reason = reason or 'forcedB-in-O'
            h += 1
        elif d == -1:
            if c in Oset: reason = reason or 'forcedB-in-O'
            h += 1
        else:
            reason = reason or 'axis|D|>=2'
    if reason is None:
        if h > B: reason = 'h>14'
        elif (B - h) % 2: reason = 'h-odd'
        elif (B - h) // 2 > v: reason = 'k>v'
    return e5, reason

e5_all = collections.Counter()
e5ge3_death = collections.Counter()
n_cfg = 0
for par in (0, 1):
    fibers = [par + 2 * t for t in range(A)]
    for O in itertools.combinations(fibers, R):
        Oset = set(O)
        for m in range(1 << (R - 1)):
            n_cfg += 1
            e5, reason = profile(O, m, Oset)
            e5_all[e5] += 1
            if e5 >= 3:
                e5ge3_death[reason] += 1
print(f"parity-pure configs scanned: {n_cfg}")
print(f"e5 census over ALL parity-pure configs: {dict(sorted(e5_all.items()))}")
print(f"e5>=3 death reasons (None = live!): {dict(e5ge3_death)}")

# ---- node table ----
cls = json.load(open('/tmp/r5tax/classes.json'))
nodes = {}
for r in cls:
    vC = collections.Counter()
    for t in r['sig']: vC[TYPES[tuple(t)]] += 1
    zl, zh = r['sig8']
    z8 = (zl or '-') + '|' + (zh or '-')
    nz = sum(vC.values())
    E0 = 16 - 1 - nz
    key = (vC['a'], vC['q'], vC['p5'], vC['f3'], z8, E0)
    if key not in nodes:
        nodes[key] = dict(np=vC['np'], no=vC['no'], h=r['h'], v=r['v'], w=r['w'],
                          n=0, eps=collections.Counter())
    nd = nodes[key]
    assert (nd['np'], nd['no'], nd['h'], nd['v'], nd['w']) == \
           (vC['np'], vC['no'], r['h'], r['v'], r['w'])
    nd['n'] += 1; nd['eps'][r['eps']] += 1
print(f"\nNODE TABLE: {len(nodes)} nodes")
print("  a q p5 f3  z8       E0 | np no  h  v  w/cls | classes  ways  eps0/eps1")
tc = tw = 0
rows = sorted(nodes.items(), key=lambda kv: (-kv[1]['n'] * kv[1]['w'], kv[0]))
for (a_, q_, p5_, f3_, z8, E0), nd in rows:
    ways = nd['n'] * nd['w']
    tc += nd['n']; tw += ways
    print(f"  {a_} {q_}  {p5_}  {f3_}  {z8:8s} {E0:2d} | {nd['np']:2d} {nd['no']:2d} "
          f"{nd['h']:2d} {nd['v']:2d} {nd['w']:4d} | {nd['n']:6d} {ways:6d}  "
          f"{nd['eps'][0]}/{nd['eps'][1]}")
print(f"  CROSSFOOT: classes {tc}  ways {tw}")
with open('/tmp/r5tax/node_table.json', 'w') as f:
    json.dump([{'a':k[0],'q':k[1],'p5':k[2],'f3':k[3],'z8':k[4],'E0':k[5],
                **{x: nodes[k][x] for x in ('np','no','h','v','w','n')},
                'eps0': nodes[k]['eps'][0], 'eps1': nodes[k]['eps'][1]}
               for k, _ in rows for k in [k]], f, indent=0)

#!/usr/bin/env python3
"""Independent structural engine for the r=5 marginal stratum at s=32 (n=64).

Enumerates ONLY parity-pure (O, mask) configs (L1, proven separately), classifies
each axis by occupancy type, applies the B-placement rule ways = C(v, (14-h)/2),
and cross-checks the resulting class set EXACTLY against the audit enumerator's
records (rec5.txt), which swept ALL O-sets (mixed parity included).

Outputs: class-level invariants (events, axis-8 descriptor, node signature),
aggregate censuses (eps split, E5 census, z*-axis strata via binomial splitting,
node table), and the B-injectivity check.
"""
import sys, itertools, collections
from math import comb

S, N, A, R, B = 32, 64, 16, 5, 14   # s, n=2s, axes=s/2, r, b
LSLOT = 3 * S // 2                   # 48 = exponent of -z*; axis 8, heavy side

def axis_side(slot):
    """slot (even) -> (axis, side); side 0 = 'light' (slot=2c), 1 = 'heavy' (2c+32)."""
    c = (slot % S) // 2
    return c, 0 if slot < S else 1

def classify(O, m):
    """O: sorted tuple of 5 fibers (parity-pure), m: 4-bit sign mask (a0 = O0).
    Returns None if dead, else dict of invariants."""
    a = [O[0]] + [O[i] + S * ((m >> (i - 1)) & 1) for i in range(1, R)]
    # term list: (axis, side, letter)
    terms = []
    prods = []
    for i in range(R):
        for j in range(i + 1, R):
            sl = (a[i] + a[j]) % N
            assert sl % 2 == 0  # parity-pure => all products even
            prods.append((i, j, sl))
            terms.append((*axis_side(sl), 'P'))
    for o in O:
        terms.append((*axis_side((2 * o) % N), 'O'))
    terms.append((*axis_side(LSLOT), 'L'))
    # per-axis occupancy
    occ = [([], []) for _ in range(A)]
    for c, sd, t in terms:
        occ[c][sd].append(t)
    oax = {}
    for o in O:
        oax.setdefault(o % A, []).append(o)
    # liveness + h, v
    h = v = 0
    forced = []; freeax = []
    for c in range(A):
        d = len(occ[c][0]) - len(occ[c][1])   # light - heavy
        has_o = c in oax
        if d == 0:
            if not has_o:
                v += 1; freeax.append(c)
        elif d == 1:      # light excess -> B on heavy fiber c+A
            if (c + A) in O: return None
            h += 1; forced.append(c + A)
        elif d == -1:     # heavy excess -> B on light fiber c
            if c in O: return None
            h += 1; forced.append(c)
        else:
            return None
    if h > B or (B - h) % 2: return None
    k = (B - h) // 2
    if k > v: return None
    w = comb(v, k)
    # events
    e1 = sum(1 for c, os_ in oax.items() if len(os_) == 2)
    e5 = e6 = 0
    seen_pp = set()
    for x in range(len(prods)):
        i, j, sl = prods[x]
        for y in range(x + 1, len(prods)):
            k2, l2, sl2 = prods[y]
            if (sl - sl2) % N == S or (sl2 - sl) % N == S:
                assert len({i, j, k2, l2}) == 4, "antipodal products share an index!"
                e5 += 1
            if sl == sl2:
                assert len({i, j, k2, l2}) == 4, "equal products share an index!"
                e6 += 1
    # P-O coincidences
    e7 = e8 = 0
    for (_, _, sl) in prods:
        for o in O:
            so = (2 * o) % N
            if (sl - so) % N == S: e7 += 1
            if sl == so: e8 += 1
    e3 = sum(1 for (_, _, sl) in prods if sl == S // 2)     # P at slot 16 (antipodal to L)
    e3p = sum(1 for (_, _, sl) in prods if sl == LSLOT)     # P at slot 48 (L3 break)
    e4 = 1 if (S // 4) in O else 0                           # o=8
    e4p = 1 if (3 * S // 4) in O else 0                      # o=24
    # axis-8 descriptor: base occupants per side (light = slot 16, heavy = slot 48)
    z_l = sorted(occ[S // 4][0]); z_h = sorted(occ[S // 4][1])
    z_forced = None
    if (S // 4) in [f % A for f in forced]:
        for f in forced:
            if f % A == S // 4:
                z_forced = 0 if f < A else 1  # wait: fiber f < A means fiber index c (light)
    zfree = (S // 4) in freeax
    # node signature: axis types (other axes side-normalized), axis-8 oriented
    types = []
    for c in range(A):
        l, hv = sorted(occ[c][0]), sorted(occ[c][1])
        if not l and not hv: continue
        if c == S // 4:
            continue  # handled separately
        pair = tuple(sorted((''.join(l), ''.join(hv))))
        types.append(pair)
    z8 = (''.join(z_l), ''.join(z_h))
    sig = (z8, tuple(sorted(types)))
    return dict(h=h, v=v, k=k, w=w, forced=sorted(forced), freeax=sorted(freeax),
                e1=e1, e5=e5, e6=e6, e7=e7, e8=e8, e3=e3, e3p=e3p, e4=e4, e4p=e4p,
                z_l=z_l, z_h=z_h, z_forced=z_forced, zfree=zfree, sig=sig)

def main():
    classes = {}
    for par in (0, 1):
        fibers = [par + 2 * t for t in range(A)]
        for O in itertools.combinations(fibers, R):
            for m in range(1 << (R - 1)):
                r = classify(O, m)
                if r is not None:
                    r['eps'] = par
                    classes[(O, m)] = r
    print(f"engine: live (O,mask) classes = {len(classes)}")
    wsum = sum(r['w'] for r in classes.values())
    print(f"engine: waysum = {wsum}")

    # ---- exact cross-check against the audit enumerator's records ----
    recs = {}
    for line in open('/tmp/r5tax/rec5.txt'):
        if not line.startswith('REC'): continue
        body = line[4:].split('|')
        O = tuple(int(x) for x in body[0].split())
        m = int(body[1])
        hpart = body[2].split(':'); h = int(hpart[0].split()[1])
        forced = sorted(int(x) for x in hpart[1].split())
        vpart = body[3].split(':'); v = int(vpart[0].split()[1])
        freeax = sorted(int(x) for x in vpart[1].split())
        w = int(body[4].split()[1])
        recs[(O, m)] = (h, forced, v, freeax, w)
    assert set(recs) == set(classes), \
        f"class-set mismatch: only-audit {len(set(recs)-set(classes))}, only-engine {len(set(classes)-set(recs))}"
    for key, (h, fr, v, fx, w) in recs.items():
        r = classes[key]
        assert (r['h'], r['forced'], r['v'], r['freeax'], r['w']) == (h, fr, v, fx, w), (key, r, (h, fr, v, fx, w))
    print("GATE: exact (O,mask,h,forced,v,free,w) equality with audit enumerator: PASS")

    # ---- aggregate censuses ----
    eps_w = collections.Counter(); eps_c = collections.Counter()
    e5_census = collections.Counter()
    for r in classes.values():
        eps_w[r['eps']] += r['w']; eps_c[r['eps']] += 1
        e5_census[r['e5']] += 1
    print(f"eps split (ways): eps0={eps_w[0]} eps1={eps_w[1]}  [target 49768/49744]")
    print(f"eps split (classes): eps0={eps_c[0]} eps1={eps_c[1]}")
    print(f"E5 census (classes): {dict(sorted(e5_census.items()))}  [target 0:3768 1:7880 2:160]")

    # ---- z*-axis strata via binomial splitting (NO B-enumeration) ----
    strata = collections.Counter()
    for r in classes.values():
        base_l = list(r['z_l']); base_h = list(r['z_h'])
        if r['z_forced'] is not None:
            (base_l if r['z_forced'] == 0 else base_h).append('B')
        def label(l, hv):
            sl, sh = ''.join(sorted(l)), ''.join(sorted(hv))
            return '|'.join(sorted([sl, sh]))
        if r['zfree']:
            # C(v-1,k-1) completions take the axis-8 B pair, C(v-1,k) don't
            wq = comb(r['v'] - 1, r['k'] - 1) if r['k'] >= 1 else 0
            wn = comb(r['v'] - 1, r['k'])
            assert wq + wn == r['w']
            if wq: strata[label(base_l + ['B'], base_h + ['B'])] += wq
            if wn: strata[label(base_l, base_h)] += wn
        else:
            strata[label(base_l, base_h)] += r['w']
    print("z*-axis strata (ways-weighted):")
    for k_, v_ in sorted(strata.items(), key=lambda t: -t[1]):
        print(f"   {k_:8s} {v_}")
    print(f"   strata crossfoot = {sum(strata.values())}")

    # ---- event-level censuses ----
    ev_keys = ['e1', 'e5', 'e6', 'e7', 'e8', 'e3', 'e3p', 'e4', 'e4p']
    for ek in ev_keys:
        cnt = collections.Counter(r[ek] for r in classes.values())
        print(f"{ek} census (classes): {dict(sorted(cnt.items()))}")

    # ---- (h,v) joint census + node table ----
    hv = collections.Counter((r['h'], r['v']) for r in classes.values())
    print("(h,v) census (classes):")
    for (h, v), c in sorted(hv.items()):
        print(f"   h={h:2d} v={v:2d}: classes {c:6d} ways-each {comb(v,(B-h)//2):4d} ways {c*comb(v,(B-h)//2)}")
    print(f"   (h,v) ways crossfoot = {sum(c*comb(v,(B-h)//2) for (h,v),c in hv.items())}")

    # node table by full signature
    nodes = collections.Counter()
    node_meta = {}
    for r in classes.values():
        key = (r['eps'], r['sig'], r['h'], r['v'])
        nodes[key] += 1
        node_meta[key] = r['w']
    print(f"node count (eps,sig,h,v): {len(nodes)} distinct nodes")
    # axis-type inventory (non-axis-8)
    inv = collections.Counter(); inv8 = collections.Counter()
    for r in classes.values():
        for t in r['sig'][1]:
            inv[t] += 1
        inv8[r['sig'][0]] += 1
    print("axis-type inventory, non-z* axes (class-weighted):")
    for t, c in sorted(inv.items(), key=lambda x: -x[1]):
        print(f"   {t}: {c}")
    print("axis-8 base-occupancy inventory (class-weighted):")
    for t, c in sorted(inv8.items(), key=lambda x: -x[1]):
        print(f"   16:{t[0] or '-'} | 48:{t[1] or '-'} : {c}")

    # ---- B-injectivity across classes ----
    seen = {}
    dup = 0
    for key, r in classes.items():
        base = frozenset(r['forced'])
        for sub in itertools.combinations(r['freeax'], r['k']):
            Bset = base | frozenset(x for c in sub for x in (c, c + A))
            if Bset in seen: dup += 1
            seen[Bset] = key
    print(f"B-injectivity: {len(seen)} distinct B-sets, duplicates {dup}  [target 99512 / 0]")

    # dump class table for downstream scripts
    import json
    with open('/tmp/r5tax/classes.json', 'w') as f:
        json.dump([{'O': list(k[0]), 'm': k[1],
                    **{x: r[x] for x in ('eps','h','v','k','w','e1','e5','e6','e7','e8','e3','e3p','e4','e4p','zfree')},
                    'z_l': r['z_l'], 'z_h': r['z_h'], 'z_forced': r['z_forced'],
                    'sig8': r['sig'][0], 'sig': [list(t) for t in r['sig'][1]]}
                   for k, r in classes.items()], f)
    print("wrote classes.json")

if __name__ == '__main__':
    main()

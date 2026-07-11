#!/usr/bin/env python3
"""Lane A char-0 lift: run the whole witness/dense construction and the
exactness check EXACTLY over Z[zeta_32] = Z[x]/(x^16+1).

If the dense layer and all agreement sets match the mod-p runs, and all
witness-dense differences at non-agreement points are NONZERO in the ring,
then the exactness law is a characteristic-0 theorem, and at a split prime
p it can only fail if p divides one of finitely many nonzero algebraic
norms (a finite, explicit bad set).
"""
import json, random
from itertools import combinations

N = 16  # Z[x]/(x^16+1), zeta = x, zeta^16 = -1, mu32 = <zeta>
ZERO = (0,) * N
ONE = (1,) + (0,) * (N - 1)


def zpow(k):
    k %= 32
    v = [0] * N
    if k < 16:
        v[k] = 1
    else:
        v[k - 16] = -1
    return tuple(v)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def mul_zpow(v, k):
    """v * zeta^k via shift with sign wrap."""
    k %= 32
    s = 1
    if k >= 16:
        k -= 16
        s = -1
    out = [0] * N
    for i, c in enumerate(v):
        if c:
            j = i + k
            if j < 16:
                out[j] += s * c
            else:
                out[j - 16] -= s * c
    return tuple(out)


def mul(a, b):
    out = [0] * N
    for i, c in enumerate(a):
        if c:
            for j, d in enumerate(b):
                if d:
                    k = i + j
                    if k < 16:
                        out[k] += c * d
                    else:
                        out[k - 16] -= c * d
    return tuple(out)


def mul_sparse_factor(acc, kpow, t):
    """acc * (zeta^kpow - t) where t is a ring element."""
    return sub(mul_zpow(acc, kpow), mul(acc, t))


LAM = neg(zpow(8))  # lam = -i, i = zeta^8

# --- witnesses ---------------------------------------------------------
# antipodal pairs of mu16 = {zeta^{2j}}: {zeta^{2j}, -zeta^{2j}=zeta^{2j+16}}
# i.e. exponent pairs (2j, 2j+16), j=0..7. i4 = zeta^8 -> exclude j=4.
PAIR_J = [j for j in range(8) if j != 4]


def witness_list():
    """Returns list of dicts: S as exponent list (exponents mod 32 of
    elements, with sign folded in as exponent+16), ew values on H (32),
    Tw."""
    out = []
    for combo in combinations(PAIR_J, 4):
        Sexp = [8]
        for j in combo:
            Sexp.extend((2 * j, 2 * j + 16))
        # e_w(zeta^k) = prod_{s} (zeta^{2k} - zeta^{se})
        ew = []
        for k in range(32):
            acc = ONE
            for se in Sexp:
                acc = sub(mul_zpow(acc, 2 * k), mul_zpow(acc, se))
            ew.append(acc)
        Tw = frozenset(k for k in range(32) if ew[k] == ZERO)
        assert len(Tw) == 18
        out.append(dict(Sexp=tuple(sorted(Sexp)), ew=ew, Tw=Tw))
    assert len(out) == 35
    return out


# --- dense -------------------------------------------------------------

def dense_list(verbose=True):
    # triples of H indices a<b<c (zeta^a etc.)
    tripV = {}
    for a, b, c in combinations(range(32), 3):
        e1 = add(add(zpow(a), zpow(b)), zpow(c))
        e2 = add(add(zpow(a + b), zpow(a + c)), zpow(b + c))
        V = sub(e2, mul(e1, e1))
        tripV.setdefault(V, []).append((a, b, c))
    found = {}
    construct = []
    for B in combinations(range(16), 7):  # exponents 2*j for j in B
        K = LAM
        for j in B:
            K = add(K, zpow(2 * j))
        trips = tripV.get(K)
        if not trips:
            continue
        for (a, b, c) in trips:
            xi = neg(add(add(zpow(a), zpow(b)), zpow(c)))
            ev = []
            for k in range(32):
                acc = ONE
                for j in B:                       # (zeta^{2k} - zeta^{2j})
                    acc = sub(mul_zpow(acc, 2 * k), mul_zpow(acc, 2 * j))
                for e in (a, b, c):               # (zeta^k - zeta^e)
                    acc = sub(mul_zpow(acc, k), mul_zpow(acc, e))
                acc = sub(mul_zpow(acc, k), mul(acc, xi))  # (zeta^k - xi)
                ev.append(acc)
            T = frozenset(k for k in range(32) if ev[k] == ZERO)
            if len(T) != 17:
                continue
            key = tuple(ev)
            if key not in found:
                found[key] = dict(B=B, x=(a, b, c), xi=xi, Tt=T, ev=ev)
                construct.append((B, (a, b, c)))
    if verbose:
        print(f"char0 dense: {len(found)}")
    return found, construct


def main():
    wits = witness_list()
    dens, construct = dense_list()
    print(f"witnesses=35 dense={len(dens)}")

    # cross-check constructions against BabyBear mod-p run
    bb = json.load(open('/tmp/laneA/result_2013265921.json'))
    print("BabyBear dense count:", bb['n_dense'], "char0:", len(dens),
          "match" if bb['n_dense'] == len(dens) else "MISMATCH")

    # exactness in char 0: for all witness-dense pairs, all k not in
    # Tw | Tt, require ew[k] != et[k] (both nonzero there by construction)
    dlist = list(dens.values())
    n_checked = 0
    viols = []
    inter_hist = {}
    for wi, w in enumerate(wits):
        ew, Tw = w['ew'], w['Tw']
        for di, d in enumerate(dlist):
            et, Tt = d['ev'], d['Tt']
            inter = Tw & Tt
            li = len(inter)
            inter_hist[li] = inter_hist.get(li, 0) + 1
            for k in range(32):
                if k in Tw or k in Tt:
                    continue
                n_checked += 1
                if ew[k] == et[k]:
                    viols.append((wi, di, k))
    print(f"witness-dense pairs=35*{len(dlist)}={35*len(dlist)}")
    print(f"char0 nonagreement value-checks={n_checked} "
          f"violations={len(viols)}")
    print("inter hist:", dict(sorted(inter_hist.items())))

    # dense-dense on the same seed-1 sample of 12000 index pairs
    allpairs = list(combinations(range(len(dlist)), 2))
    rng = random.Random(1)
    samp = rng.sample(allpairs, 12000) if len(allpairs) > 12000 else allpairs
    eh = {}
    exc = []
    for a, b in samp:
        da, db = dlist[a], dlist[b]
        inter = da['Tt'] & db['Tt']
        z = sum(1 for k in range(32) if da['ev'][k] == db['ev'][k])
        e = z - len(inter)
        eh[e] = eh.get(e, 0) + 1
        if e > 0:
            exc.append((a, b, e))
    print("char0 dense-dense excess hist:", dict(sorted(eh.items())))
    # dump exceptional pair structure
    for a, b, e in exc:
        da, db = dlist[a], dlist[b]
        pts = [k for k in range(32) if da['ev'][k] == db['ev'][k]
               and k not in (da['Tt'] & db['Tt'])]
        print(f"  exc pair d{a},d{b} excess={e} pts={pts} "
              f"B1={da['B']} x1={da['x']} B2={db['B']} x2={db['x']} "
              f"|B1&B2|={len(set(da['B']) & set(db['B']))}")
        for k in pts:
            print(f"    shared value at k={k}: {da['ev'][k]}")
    json.dump(dict(n_dense=len(dens), n_checked=n_checked,
                   n_viol=len(viols),
                   excess_hist={str(k): v for k, v in eh.items()},
                   construct=[(list(B), list(x)) for B, x in construct]),
              open('/tmp/laneA/char0_result.json', 'w'))
    print("saved /tmp/laneA/char0_result.json")


if __name__ == '__main__':
    main()

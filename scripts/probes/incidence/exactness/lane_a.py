#!/usr/bin/env python3
"""Lane A: the exactness law for witness-dense pairs.

Setup at any split prime p = 1 (mod 32):
  g0   = smallest primitive root
  i4   = g0^((p-1)/4)          (primitive 4th root of unity, = z*)
  lam  = -i4 mod p
  h32  = g0^((p-1)/32); H = mu32 = <h32>;  G = mu16 = <h32^2>
  word w(x) = x^18 + lam x^16, code RS[F_p, H, 16] (deg < 16)

Witness layer (35 = C(7,4)): S = {i4} u (4 antipodal pairs of mu16, pair
{i4,-i4} excluded).  e_w(x) = E(x^2), E(Y) = prod_{s in S}(Y - s).
c_w = w - e_w has deg <= 14 because e1(S) = i4 = -lam.  |T_w| = 18.

Dense layer: e_t(x) = prod_{b in B}(x^2 - z_b) * (x-x1)(x-x2)(x-x3)(x-xi),
B a 7-subset of mu16, x1,x2,x3 in H, xi = -(x1+x2+x3), subject to the
consistency law e2(x)-e1(x)^2 = lam + e1(B); keep exactly-17 zeros on H.

Exactness law under attack: for every witness-dense pair the difference
d = c_w - c_t vanishes on H exactly on T_w & T_t (no accidental zeros).
All arithmetic exact (Python ints mod p).
"""
import sys, json, random
from itertools import combinations


def factor(n):
    fs = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return fs


def primitive_root(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root found")


def poly_from_roots(roots, p):
    """monic poly with given roots, coeffs low->high."""
    c = [1]
    for r in roots:
        nr = (-r) % p
        c = [0] + c
        for k in range(len(c) - 1):
            c[k] = (c[k] + nr * c[k + 1]) % p
    return c


def poly_eval(c, x, p):
    acc = 0
    for a in reversed(c):
        acc = (acc * x + a) % p
    return acc


def setup(p):
    assert (p - 1) % 32 == 0, p
    g = primitive_root(p)
    i4 = pow(g, (p - 1) // 4, p)
    lam = (-i4) % p
    h32 = pow(g, (p - 1) // 32, p)
    H = [pow(h32, k, p) for k in range(32)]
    assert len(set(H)) == 32
    mu16 = [H[2 * k] for k in range(16)]
    Hsq = [(x * x) % p for x in H]          # Hsq[k] = H[k]^2 in mu16
    assert set(Hsq) == set(mu16)
    # partner index of -x: -1 = h32^16 so -H[k] = H[(k+16)%32]
    assert (H[0] + H[16]) % p == 0
    w_evals = [(pow(x, 18, p) + lam * pow(x, 16, p)) % p for x in H]
    return dict(p=p, g=g, i4=i4, lam=lam, H=H, mu16=mu16, Hsq=Hsq,
                w=w_evals)


def witnesses(st):
    """35 witnesses; returns list of dicts with cw (eval tuple on H), Tw, S."""
    p, i4, lam, mu16, Hsq, w = (st['p'], st['i4'], st['lam'], st['mu16'],
                                st['Hsq'], st['w'])
    pairs, seen = [], set()
    for z in mu16:
        key = frozenset((z, (-z) % p))
        if key not in seen:
            seen.add(key)
            pairs.append(key)
    assert len(pairs) == 8
    pairs7 = [pr for pr in pairs if i4 not in pr]
    assert len(pairs7) == 7
    out = []
    for combo in combinations(pairs7, 4):
        S = [i4]
        for pr in combo:
            S.extend(sorted(pr))
        assert len(set(S)) == 9
        assert sum(S) % p == i4 % p          # e1(S) = i4 = -lam
        E = poly_from_roots(S, p)            # deg 9 monic
        assert E[8] == lam                   # Y^8 coeff = -e1(S) = lam
        ew = [poly_eval(E, z2, p) for z2 in Hsq]
        Tw = frozenset(k for k in range(32) if ew[k] == 0)
        assert len(Tw) == 18
        cw = tuple((w[k] - ew[k]) % p for k in range(32))
        out.append(dict(S=tuple(S), Sset=frozenset(S), cw=cw, Tw=Tw,
                        E=E))
    assert len(out) == 35
    return out


def dense(st, cap=None, verbose=False):
    """Enumerate dense words by solving the consistency equation.
    Returns dict: cw_tuple -> record (first construction found)."""
    p, lam, H, mu16, Hsq, w = (st['p'], st['lam'], st['H'], st['mu16'],
                               st['Hsq'], st['w'])
    tripV = {}
    for x1, x2, x3 in combinations(H, 3):
        e1 = (x1 + x2 + x3) % p
        e2 = (x1 * x2 + x1 * x3 + x2 * x3) % p
        V = (e2 - e1 * e1) % p
        tripV.setdefault(V, []).append((x1, x2, x3))
    found = {}
    raw = 0
    for B in combinations(mu16, 7):
        K = (lam + sum(B)) % p
        trips = tripV.get(K)
        if not trips:
            continue
        F = poly_from_roots(B, p)            # deg 7 in Y
        Fmu = {z: poly_eval(F, z, p) for z in set(Hsq)}
        e1B = sum(B) % p
        for x1, x2, x3 in trips:
            s = (x1 + x2 + x3) % p
            xi = (-s) % p
            ev, T = [], []
            for k in range(32):
                x = H[k]
                q = ((x - x1) * (x - x2) % p) * ((x - x3) * (x - xi) % p) % p
                e = Fmu[Hsq[k]] * q % p
                ev.append(e)
                if e == 0:
                    T.append(k)
            if len(T) != 17:
                continue
            raw += 1
            ct = tuple((w[k] - ev[k]) % p for k in range(32))
            if ct not in found:
                # e3 of the quartic (x1,x2,x3,xi)
                e3 = (x1 * x2 * x3 + x1 * x2 * xi + x1 * x3 * xi
                      + x2 * x3 * xi) % p
                found[ct] = dict(B=tuple(B), Bset=frozenset(B),
                                 x=(x1, x2, x3), xi=xi,
                                 xi_in_H=xi in set(H),
                                 e3=e3, Tt=frozenset(T), ct=ct,
                                 e1B=e1B)
            if cap and len(found) >= cap:
                if verbose:
                    print(f"  dense cap {cap} reached (raw {raw})")
                return found, raw
    return found, raw


def check_pairs(wits, dens, st, dense_keys=None):
    """Check the exactness law on all witness-dense pairs.
    Returns (n_pairs, violations, inter_hist).
    violation record: (wi, ct, extra zero indices, dead_fiber_flags)."""
    p = st['p']
    viols = []
    inter_hist = {}
    keys = dense_keys if dense_keys is not None else list(dens.keys())
    n = 0
    for wi, wrec in enumerate(wits):
        cw, Tw = wrec['cw'], wrec['Tw']
        for ct in keys:
            drec = dens[ct]
            Tt = drec['Tt']
            inter = Tw & Tt
            Z = frozenset(k for k in range(32) if cw[k] == ct[k])
            assert inter <= Z
            li = len(inter)
            inter_hist[li] = inter_hist.get(li, 0) + 1
            n += 1
            if Z != inter:
                extra = sorted(Z - inter)
                dead = [((k + 16) % 32) in Z for k in extra]
                viols.append(dict(wi=wi, S=wrec['S'], B=drec['B'],
                                  x=drec['x'], xi=drec['xi'],
                                  extra=extra, partner_also_zero=dead,
                                  n_extra=len(extra)))
    return n, viols, inter_hist


def check_dense_dense(dens, st, sample=None, seed=1):
    """Excess-zero stats on dense-dense pairs."""
    p = st['p']
    keys = list(dens.keys())
    allpairs = list(combinations(range(len(keys)), 2))
    if sample and len(allpairs) > sample:
        rng = random.Random(seed)
        allpairs = rng.sample(allpairs, sample)
    excess_hist = {}
    examples = []
    for a, b in allpairs:
        ka, kb = keys[a], keys[b]
        Ta, Tb = dens[ka]['Tt'], dens[kb]['Tt']
        inter = Ta & Tb
        Z = sum(1 for k in range(32) if ka[k] == kb[k])
        ex = Z - len(inter)
        excess_hist[ex] = excess_hist.get(ex, 0) + 1
        if ex > 0 and len(examples) < 20:
            examples.append((a, b, ex))
    return len(allpairs), excess_hist, examples


def run_prime(p, dense_cap=None, dd_sample=None, verbose=True):
    st = setup(p)
    wits = witnesses(st)
    dens, raw = dense(st, cap=dense_cap, verbose=verbose)
    res = dict(p=p, g=st['g'], lam=st['lam'], i4=st['i4'],
               n_wit=len(wits), n_dense=len(dens), n_dense_raw=raw)
    if verbose:
        print(f"p={p} g0={st['g']} lam={st['lam']} z*=i4={st['i4']} "
              f"witnesses={len(wits)} dense={len(dens)} (raw {raw})")
    if dens:
        e3zero = sum(1 for d in dens.values() if d['e3'] == 0)
        xiH = sum(1 for d in dens.values() if d['xi_in_H'])
        n, viols, ih = check_pairs(wits, dens, st)
        res.update(n_pairs=n, n_viol_pairs=len(viols),
                   n_extra_zeros=sum(v['n_extra'] for v in viols),
                   dead_fiber_accidents=sum(any(v['partner_also_zero'])
                                            for v in viols),
                   e3_zero_dense=e3zero, xi_in_H_dense=xiH,
                   inter_hist={str(k): v for k, v in sorted(ih.items())},
                   viol_examples=viols[:10])
        if verbose:
            print(f"  witness-dense pairs={n} violating={len(viols)} "
                  f"extra zeros total={res['n_extra_zeros']} "
                  f"dead-fiber accidents={res['dead_fiber_accidents']}")
            print(f"  e3==0 dense: {e3zero}, xi in H: {xiH}")
            print(f"  |Tw&Tt| histogram: {res['inter_hist']}")
        if dd_sample:
            ndd, eh, ex = check_dense_dense(dens, st, sample=dd_sample)
            res.update(dd_pairs=ndd,
                       dd_excess_hist={str(k): v for k, v in
                                       sorted(eh.items())})
            if verbose:
                print(f"  dense-dense pairs={ndd} excess hist={res['dd_excess_hist']}")
    return res


if __name__ == '__main__':
    p = int(sys.argv[1])
    cap = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] != '-' else None
    dd = int(sys.argv[3]) if len(sys.argv) > 3 else None
    res = run_prime(p, dense_cap=cap, dd_sample=dd)
    out = f"/tmp/laneA/result_{p}.json"
    with open(out, 'w') as f:
        json.dump(res, f, indent=1, default=str)
    print("saved", out)

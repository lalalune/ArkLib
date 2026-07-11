"""GENERAL-s LEVEL-2 ENGINE (the DERIVED-672 recipe, parameterized by s = 2^j).

Setup: n = 2s, H = mu_n, G = mu_s (fibers z in Z_s, roots zeta^{z + s*d}), word
w = X^{s+2} + lam X^s, lam = -z*, z* = zeta^{s/2} (canonical 4th root in mu_s,
fiber s/4 in Z_s; -z* at fiber 3s/4).  Marginal (agree exactly k+1 = s+1) layer:
  e = Prod_{b in B}(X^2 - z_b) (X-x1)(X-x2)(X-x3)(X-xi),  |B| = s/2-1, |O| = 3,
  xi = -(x1+x2+x3).
PROVEN REDUCTION (pure algebra, s-independent): consistency
  e2(x) - e1(x)^2 = lam + e1(B_z)
<=> vanishing of the (s/2+6)-term mu_n multiset
  {x1x2, x1x3, x2x3} U B_z U O_z U {-z*}
<=> ANTIPODAL BALANCE in the power basis of Z[zeta_n], n = 2^{j+1}
  (2-power Lam-Leung, multiset form):  mult(zeta^m) = mult(zeta^{m+s}) for all m.

This enumerator assumes ONLY the reduction + the placement logic (B = s/2-1
distinct fibers disjoint from O; forced/free-axis rule).  All lemmas (parity,
axis-distinctness, sigma-uniqueness, ...) are RE-VERIFIED per s, not assumed.
"""
from itertools import combinations
from math import comb
from collections import Counter, defaultdict

SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]  # (s12,s13,s23), xor = 0


def run(s, collect_elements=True):
    n = 2 * s
    A = s // 2            # number of even (fiber-pair) axes, indexed c in Z_{s/2}
    bsz = s // 2 - 1      # |B|
    Lfib = 3 * s // 4     # fiber of -z*  (exponent 2*Lfib = 3s/2)
    Laxis = (Lfib) % A    # = s/4

    sols = []             # (B frozenset, O tuple, sig tuple)
    recs = []             # class records
    mixed_feasible = 0

    for O in combinations(range(s), 3):
        Oset = set(O)
        pure = (O[0] % 2 == O[1] % 2 == O[2] % 2)
        for sig in SIGS:
            d = (0, sig[0], sig[1])
            a = [O[i] + s * d[i] for i in range(3)]      # zeta-exponents of x_i
            terms = [(2 * O[0]) % n, (2 * O[1]) % n, (2 * O[2]) % n,
                     (a[0] + a[1]) % n, (a[0] + a[2]) % n, (a[1] + a[2]) % n,
                     (2 * Lfib) % n]
            cnt = [0] * n
            for t in terms:
                cnt[t] += 1
            feasible = True
            # odd axes: B cannot contribute -> need outright balance
            for m in range(1, s, 2):
                if cnt[m] != cnt[m + s]:
                    feasible = False
                    break
            forced, freeax = [], []
            if feasible:
                for c in range(A):
                    dd = cnt[2 * c] - cnt[(2 * c + s) % n]
                    if abs(dd) >= 2:
                        feasible = False
                        break
                    if dd == -1:
                        f = c                 # light side = fiber c
                    elif dd == 1:
                        f = c + A             # light side = fiber c + s/2
                    else:
                        if c not in Oset and (c + A) not in Oset:
                            freeax.append(c)
                        continue
                    if f in Oset:
                        feasible = False
                        break
                    forced.append(f)
            if not feasible:
                continue
            h, v = len(forced), len(freeax)
            if (bsz - h) < 0 or (bsz - h) % 2 != 0 or (bsz - h) // 2 > v:
                continue
            k = (bsz - h) // 2
            ways = comb(v, k)
            recs.append(dict(O=O, sig=sig, h=h, v=v, k=k, ways=ways,
                             forced=tuple(sorted(forced)), freeaxes=tuple(freeax),
                             pure=pure))
            if not pure:
                mixed_feasible += ways
            if collect_elements:
                for pick in combinations(freeax, k):
                    B = frozenset(forced) | {c for c in pick} | {c + A for c in pick}
                    assert len(B) == bsz and not (B & Oset)
                    sols.append((B, O, sig))
    return dict(s=s, A=A, bsz=bsz, Lfib=Lfib, Laxis=Laxis, sols=sols, recs=recs,
                mixed_feasible=mixed_feasible)


def label(s, O, sig):
    """Event taxonomy E1-E4, generalized (all conditions derived mod 2-powers)."""
    m = s // 2
    M = m // 2
    eps = O[0] % 2
    if not (O[0] % 2 == O[1] % 2 == O[2] % 2):
        return None
    u = tuple((o - eps) // 2 for o in O)             # subset of Z_m
    sT = sum(u) % m
    E1 = any((u[j] - u[i]) % m == M for i in range(3) for j in range(3) if i < j)
    inv3 = pow(3, -1, m)
    E2 = (inv3 * sT) % m in u
    E3 = (sT - (M - eps)) % m in u
    E4 = tuple(sorted(o for o in O if o % m == s // 4))   # o in {s/4, 3s/4}
    return (eps, E1, E2, E3, E4)


def analyze(R, verbose=True):
    s, A, sols, recs = R['s'], R['A'], R['sols'], R['recs']
    n = 2 * s
    out = {}
    ncls = len(sols)
    out['classes'] = ncls
    out['elements'] = 2 * ncls
    out['mixed_feasible'] = R['mixed_feasible']

    # L5: sigma-uniqueness per (B,O)
    BO = defaultdict(set)
    for B, O, sig in sols:
        BO[(B, O)].add(sig)
    out['sigma_unique'] = all(len(v) == 1 for v in BO.values())

    # eps split (classes)
    epsc = Counter(O[0] % 2 for B, O, sig in sols)
    out['eps_split'] = dict(epsc)

    # B census -> {2,4} menu
    Bcnt = Counter(B for B, O, sig in sols)
    mh = Counter(Bcnt.values())
    out['distinct_B'] = len(Bcnt)
    out['B_mult_hist'] = dict(sorted(mh.items()))

    # dual-B mechanisms
    perB = defaultdict(list)
    for B, O, sig in sols:
        perB[B].append((O, sig))
    mech = Counter()
    for B, v in perB.items():
        if len(v) == 2:
            (O1, s1), (O2, s2) = v
            i = set(O1) & set(O2)
            if i:
                mech[('share%d' % len(i),)] += 1
            else:
                sh4 = frozenset((o + s // 4) % s for o in O1) == frozenset(O2)
                shm4 = frozenset((o - s // 4) % s for o in O1) == frozenset(O2)
                mech[('disjoint', 'shift_s4' if (sh4 or shm4) else 'other')] += 1
        elif len(v) > 2:
            mech[('MULT%d' % len(v),)] += 1
    out['dualB'] = dict(mech)
    out['dualB_total'] = sum(c for k, c in mech.items() if not k[0].startswith('MULT'))

    # z*-axis (L-axis) slot strata per class
    Laxis = R['Laxis']
    Lf = R['Lfib']
    strat = Counter()
    for B, O, sig in sols:
        d = (0, sig[0], sig[1])
        a = [O[i] + s * d[i] for i in range(3)]
        lo, hi = [], []   # fiber s/4 side, fiber 3s/4 side
        slots = {Laxis: lo, (Laxis + A): hi}
        def put(fib, tag):
            if fib == s // 4:
                lo.append(tag)
            elif fib == 3 * s // 4:
                hi.append(tag)
        for o in O:
            put(o, 'O')
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            e = (a[i] + a[j]) % n
            if e % 2 == 0:
                put((e // 2) % s, 'P')
        put(Lf, 'L')
        for b in B:
            put(b, 'B')
        key = '|'.join(sorted([''.join(sorted(lo)), ''.join(sorted(hi))]))
        strat[key] += 1
    out['Laxis_strata'] = dict(strat.most_common())

    # node table: (label, h, v, k) -> class count, ways
    groups = defaultdict(list)
    for r in recs:
        lab = label(s, r['O'], r['sig'])
        groups[(lab, r['h'], r['v'], r['k'])].append(r)
    table = []
    for key in sorted(groups, key=lambda t: (str(t[0]), t[1])):
        lab, h, v, k = key
        cls = len(groups[key])
        w = comb(v, k)
        assert all(r['ways'] == w for r in groups[key])
        table.append((lab, h, v, k, cls, w, cls * w))
    out['node_table'] = table
    assert sum(t[-1] for t in table) == ncls

    # event multiplicity sanity (no double events)
    out['taxonomy_closed'] = True
    for r in recs:
        m = s // 2
        eps = r['O'][0] % 2
        if not all(o % 2 == eps for o in r['O']):
            out['taxonomy_closed'] = False
    if verbose:
        print(f"== s = {s} (n = {n}) ==")
        print(f"  feasible (B,O,sigma) classes: {ncls}   elements: {2*ncls}")
        print(f"  mixed-parity feasible: {R['mixed_feasible']}  (L1 holds iff 0)")
        print(f"  sigma-unique per (B,O) (L5): {out['sigma_unique']}")
        print(f"  eps split (classes): {out['eps_split']}")
        print(f"  distinct B: {out['distinct_B']}  multiplicity hist: {out['B_mult_hist']}")
        print(f"  dual-B mechanisms: {out['dualB']}")
        print(f"  z*-axis strata: {out['Laxis_strata']}")
        print(f"  node table ((eps,E1,E2,E3,E4), h, v, k, #cls, C(v,k), subtotal):")
        for lab, h, v, k, cls, w, sub in table:
            print(f"    {str(lab):42s} h={h} v={v:2d} k={k:2d}  #cls={cls:4d}"
                  f"  C={w:4d}  sub={sub:5d}")
    return out


if __name__ == '__main__':
    import sys
    for s in (int(x) for x in sys.argv[1:] or [8, 16, 32]):
        analyze(run(s))
        print()

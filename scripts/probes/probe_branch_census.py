#!/usr/bin/env python3
"""
P3 BRANCH-TREE CENSUS (falsify-first probe).

Object: window-vanishing valued errors that are CODEWORD DIFFERENCES:
  e = evaluation on mu_n subset F_p^* of a polynomial f, deg f <= n - t, e != 0.
  (Then sum_{x in mu_n} e(x) x^s = n * a_{(n-s) mod n} = 0 for s = 1..t-1;
   s = 0 gives n*a_0, i.e. the full in-tree window j < t additionally needs a_0 = 0.)

Fold tree (O56/O57 / LamLeungTwoPow.foldVal/foldValOdd):
  even(y) = e(x) + e(-x),  odd(y) = (e(x) - e(-x)) * x   at  y = x^2.
Each branch is again a valued error on mu_{n/2}; recurse.  Depth ell branches
live on mu_{n/2^ell}; ALIVE = branch not identically zero.  Measure alive count
and per-branch support sizes at each depth ell <= log2(n) - 1.

Exact arithmetic mod p everywhere (ints); floats only in print formatting.

Internal exact law being tested (derived by hand, verified per-sample here):
  write f = sum_r x^r f_r(x^{2^ell}) over residues r mod 2^ell. Then the depth-ell
  branch indexed by r equals 2^ell * Y^{delta_r} * f^{(r)}(Y) on mu_{n/2^ell}
  (delta_r in {0,1}), hence
    RESIDUE LAW:  alive(ell) = #{ r mod 2^ell : some coeff a_k != 0 with k = r mod 2^ell }
    SUPPORT LAW:  branch_r support = #{ y in mu_{n/2^ell} : f^{(r)}(y) != 0 }.

Hypotheses tested per sample (violations counted; expectation in brackets):
  H_residue_alive   tree alive == residue-law alive               [0 violations]
  H_residue_supp    tree support multiset == residue prediction   [0, subsample]
  H_mono            alive(ell) <= alive(ell+1) <= 2*alive(ell)    [0]
  H_pow2            alive(ell)=1  =>  2^ell | (n - w)             [0]
  H_frontier        w >= ceil(t/2^ell) * ceil(2^ell / alive(ell)) [0?  the sharp one]
  H_task            alive(ell) <= w*2^ell/t (task's suggested bd) [0 but VACUOUS: w>=t]
  H_branch_floor    every alive branch supp >= max(1,floor(t/2^ell)) [0]
  H_window          every alive branch supp >= (vanishing-syndrome run)+1 [0, subsample]
  H_root_window     root syndrome run >= t-1                      [0, subsample]
  H_scaling         alive profile+support multisets invariant under e(x)->e(cx), c in mu_n [0]
"""

import itertools
import random
import time
from collections import Counter, defaultdict
from math import comb

random.seed(20260610)

# ---------------------------------------------------------------- field/domain
def find_order_n_elem(p, n):
    assert (p - 1) % n == 0, (p, n)
    for g0 in range(2, p):
        g = pow(g0, (p - 1) // n, p)
        if pow(g, n // 2, p) != 1:
            assert pow(g, n, p) == 1
            return g
    raise ValueError("no element of order n")

# ---------------------------------------------------------------- poly helpers
def pmul(a, b, p):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    res[i + j] = (res[i + j] + ai * bj) % p
    return res

def from_roots(roots, p):
    f = [1]
    for r in roots:
        f = pmul(f, [(-r) % p, 1], p)
    return f

def peval(f, x, p):
    acc = 0
    for c in reversed(f):
        acc = (acc * x + c) % p
    return acc

# ---------------------------------------------------------------- census core
def census_e(e, p, xs_chain, L, keep=False):
    """Return levels[ell] = sorted support sizes of ALIVE branches at depth ell
    (ell = 0..L-1); if keep, also the branch value-lists per level."""
    branches = [e]
    levels = []
    blevels = [] if keep else None
    for ell in range(L):
        levels.append(sorted(sum(1 for v in b if v) for b in branches))
        if keep:
            blevels.append([b[:] for b in branches])
        if ell < L - 1:
            xs = xs_chain[ell]
            nxt = []
            for b in branches:
                h = len(b) // 2
                ev = [(b[j] + b[j + h]) % p for j in range(h)]
                od = [((b[j] - b[j + h]) * xs[j]) % p for j in range(h)]
                if any(ev):
                    nxt.append(ev)
                if any(od):
                    nxt.append(od)
            branches = nxt
    return levels, blevels

def window_run(b, xs, p):
    """largest c with sum_j b[j]*xs[j]^s == 0 for all s = 1..c."""
    m = len(b)
    pw = xs[:]
    run = 0
    for s in range(1, m + 1):
        tot = 0
        for bj, pj in zip(b, pw):
            if bj:
                tot += bj * pj
        if tot % p:
            break
        run += 1
        if s < m:
            pw = [(pj * xj) % p for pj, xj in zip(pw, xs)]
    return run

def closure_order(I, n):
    """largest 2-power d | n with index-set I a union of cosets of the order-d
    subgroup of Z_n (i.e. closed under +n/d).  Nested, so break on first fail."""
    d = 1
    dd = 2
    while dd <= n:
        st = n // dd
        if all(((i + st) % n) in I for i in I):
            d = dd
        else:
            break
        dd *= 2
    return d

# ---------------------------------------------------------------- generators
def gen_samples(n, p, t, g, scale, nrand):
    deg = n - t
    xs = [pow(g, i, p) for i in range(n)]
    out = []
    add = out.append

    # (1) minimal weight-t words: f = prod_{x in Z}(X-x), Z = mu_n \ T, |T| = t.
    nmin = 2600 if scale >= 1 else 700
    if comb(n, t) <= nmin:
        supports = itertools.combinations(range(n), t)
    else:
        supports = (tuple(random.sample(range(n), t)) for _ in range(nmin))
    for T in supports:
        Ts = set(T)
        add(('minimal', from_roots([xs[i] for i in range(n) if i not in Ts], p)))

    # (2) near-minimal: support T of size w in {t+1, t+2}; f = q * prod_{x not in T}(X-x)
    for wt in (t + 1, t + 2):
        if wt > n:
            break
        for _ in range(int(800 * scale)):
            T = set(random.sample(range(n), wt))
            base = from_roots([xs[i] for i in range(n) if i not in T], p)
            q = [random.randrange(p) for _ in range(wt - t + 1)]
            if not any(q):
                q[0] = 1
            add(('nearmin', pmul(base, q, p)))

    # (3) random dense, deg <= n-t
    for _ in range(nrand):
        f = [random.randrange(p) for _ in range(deg + 1)]
        if any(f):
            add(('random', f))
    # (3') random with a_0 = 0 (full in-tree window j < t vanishes)
    for _ in range(int(600 * scale)):
        f = [0] + [random.randrange(p) for _ in range(deg)]
        if any(f):
            add(('random_a0', f))

    # (4) monomials
    for a in range(deg + 1):
        add(('monomial', [0] * a + [1]))

    # (5) binomials x^a - c x^b  (b < a <= deg)
    for _ in range(int(1200 * scale)):
        b, a = sorted(random.sample(range(deg + 1), 2))
        c = pow(g, random.randrange(n), p)        # c in mu_n -> structured weight
        f = [0] * (b) + [(-c) % p] + [0] * (a - b - 1) + [1]
        add(('binomial', f))
    for _ in range(int(300 * scale)):
        b, a = sorted(random.sample(range(deg + 1), 2))
        c = random.randrange(1, p)
        f = [0] * (b) + [(-c) % p] + [0] * (a - b - 1) + [1]
        add(('binomial_gen', f))

    # (6) C19-style coset-vanishing: f = prod_{j in S} (X^m - g^{jm}),
    #     zero set = union of |S| cosets of mu_m, weight = n - |S|*m exactly.
    m = 2
    while m <= deg:
        if n % m == 0:
            ncos = n // m
            cap = 100 if scale >= 1 else 30
            for s in range(1, deg // m + 1):
                if comb(ncos, s) <= cap:
                    subs = itertools.combinations(range(ncos), s)
                else:
                    subs = (tuple(random.sample(range(ncos), s)) for _ in range(cap))
                for S in subs:
                    f = [1]
                    for j in S:
                        fac = [0] * (m + 1)
                        fac[0] = (-pow(g, j * m, p)) % p
                        fac[m] = 1
                        f = pmul(f, fac, p)
                    add(('coset', f))
        m *= 2

    # (7) coset-product times generic factor (near-coset weights)
    mchoices = [mm for mm in (2, 4, 8, 16) if mm <= deg and n % mm == 0]
    for _ in range(int(600 * scale)):
        m = random.choice(mchoices)
        s = random.randrange(1, deg // m + 1)
        S = random.sample(range(n // m), s)
        f = [1]
        for j in S:
            fac = [0] * (m + 1)
            fac[0] = (-pow(g, j * m, p)) % p
            fac[m] = 1
            f = pmul(f, fac, p)
        slack = deg - s * m
        if slack > 0:
            dq = random.randrange(1, slack + 1)
            q = [random.randrange(p) for _ in range(dq + 1)]
            if any(q):
                f = pmul(f, q, p)
        add(('cosetmix', f))

    # (8) sparse f
    for _ in range(int(900 * scale)):
        k = random.choice((2, 3, 4))
        exps = random.sample(range(deg + 1), min(k, deg + 1))
        f = [0] * (max(exps) + 1)
        for ee in exps:
            f[ee] = random.randrange(1, p)
        add(('sparse', f))

    return out

# ---------------------------------------------------------------- aggregation
VIOL = Counter()
VIOL_EX = {}                                   # first counterexample per violation
MAXALIVE = {}                                  # (cfg,ell) -> (A, w, fam)
FRONTIER = {}                                  # (cfg,ell,A) -> (w, fam, d, nresid)
DIST = defaultdict(lambda: [0, 10 ** 9, 0])    # (cfg,ell,w) -> [count, minA, maxA]
MINIMAL_HIST = defaultdict(Counter)            # (cfg,ell) -> Counter{A: count}  (w = t family)
RANDOM_HIST = defaultdict(Counter)
MINBSUPP = {}                                  # (cfg,ell) -> (minsupp, w, fam)
TOTRATIO = {}                                  # (cfg,ell) -> (tot, w, fam) maximizing tot/w
WINMINEX = {}                                  # (cfg,ell) -> min (supp - run) over alive branches

def viol(name, ex):
    VIOL[name] += 1
    VIOL_EX.setdefault(name, ex)

def run_config(n, p, t, scale, nrand):
    t0 = time.time()
    g = find_order_n_elem(p, n)
    L = n.bit_length() - 1                     # log2 n ; depths 0..L-1
    xs_chain = []
    gg, m = g, n
    for _ in range(L):
        xs_chain.append([pow(gg, j, p) for j in range(m)])
        gg = (gg * gg) % p
        m //= 2
    cfg = (n, p, t)
    famcount = Counter()
    rot_done = 0
    for idx, (fam, f) in enumerate(gen_samples(n, p, t, g, scale, nrand)):
        effdeg = max((k for k, c in enumerate(f) if c % p), default=-1)
        assert effdeg <= n - t, (cfg, fam, effdeg)   # hard in-model guard
        e = [peval(f, x, p) for x in xs_chain[0]]
        w = sum(1 for v in e if v)
        if w == 0:
            continue
        famcount[fam] += 1
        do_win = (idx % 4 == 0)
        levels, blevels = census_e(e, p, xs_chain, L, keep=do_win)
        nz = [k for k, c in enumerate(f) if c % p]
        zidx = frozenset(i for i in range(n) if e[i] == 0)

        for ell in range(L):
            sups = levels[ell]
            A = len(sups)
            two = 1 << ell
            # residue law (alive)
            pred = len({k % two for k in nz})
            if A != pred:
                viol('H_residue_alive', (cfg, fam, ell, A, pred, tuple(nz)[:8]))
            # bookkeeping
            ma = MAXALIVE.get((cfg, ell))
            if ma is None or A > ma[0]:
                MAXALIVE[(cfg, ell)] = (A, w, fam)
            fr = FRONTIER.get((cfg, ell, A))
            if fr is None or w < fr[0]:
                FRONTIER[(cfg, ell, A)] = (w, fam, closure_order(zidx, n),
                                           len({k % two for k in nz}))
            rec = DIST[(cfg, ell, w)]
            rec[0] += 1
            rec[1] = min(rec[1], A)
            rec[2] = max(rec[2], A)
            if fam == 'minimal':
                MINIMAL_HIST[(cfg, ell)][A] += 1
            elif fam == 'random':
                RANDOM_HIST[(cfg, ell)][A] += 1
            mb = MINBSUPP.get((cfg, ell))
            if mb is None or sups[0] < mb[0]:
                MINBSUPP[(cfg, ell)] = (sups[0], w, fam)
            tot = sum(sups)
            tr = TOTRATIO.get((cfg, ell))
            if tr is None or tot * tr[1] > tr[0] * w:
                TOTRATIO[(cfg, ell)] = (tot, w, fam)
            # hypotheses
            if A == 1 and (n - w) % two:
                viol('H_pow2', (cfg, fam, ell, w))
            B = (-(-t // two)) * (-(-two // A))
            if w < B:
                viol('H_frontier', (cfg, fam, ell, A, w, B))
            if A * t > w * two:
                viol('H_task', (cfg, fam, ell, A, w))
            if sups[0] < max(1, t // two):
                viol('H_branch_floor', (cfg, fam, ell, sups[0], w))
        for ell in range(L - 1):
            A0, A1 = len(levels[ell]), len(levels[ell + 1])
            if not (A0 <= A1 <= 2 * A0):
                viol('H_mono', (cfg, fam, ell, A0, A1))

        if do_win:
            for ell, brs in enumerate(blevels):
                xs = xs_chain[ell]
                for bi, b in enumerate(brs):
                    run = window_run(b, xs, p)
                    s = sum(1 for v in b if v)
                    if s < run + 1:
                        viol('H_window', (cfg, fam, ell, s, run))
                    key = (cfg, ell)
                    if key not in WINMINEX or s - run < WINMINEX[key]:
                        WINMINEX[key] = s - run
                    if ell == 0 and bi == 0 and run < t - 1:
                        viol('H_root_window', (cfg, fam, run, t))

        if idx % 16 == 0:                       # support law (residue prediction)
            for ell in range(L):
                two = 1 << ell
                preds = []
                for r in {k % two for k in nz}:
                    fr_ = [f[k] for k in range(r, len(f), two)]
                    preds.append(sum(1 for y in xs_chain[ell] if peval(fr_, y, p)))
                if sorted(preds) != levels[ell]:
                    viol('H_residue_supp', (cfg, fam, ell, sorted(preds), levels[ell]))

        if rot_done < 8 and idx % 97 == 0:      # scaling-orbit sanity
            for k in range(1, n):
                ek = e[k:] + e[:k]
                lv, _ = census_e(ek, p, xs_chain, L)
                if lv != levels:
                    viol('H_scaling', (cfg, fam, k))
                    break
            rot_done += 1

    return cfg, famcount, L, time.time() - t0

# ---------------------------------------------------------------- main
CONFIGS = [
    # (n, p, t, scale, n_random)
    (16, 97, 2, 1.0, 3000),
    (16, 97, 3, 1.0, 3000),
    (16, 97, 4, 1.0, 10000),
    (16, 257, 4, 0.25, 800),
    (32, 193, 2, 1.0, 3000),
    (32, 193, 3, 1.0, 3000),
    (32, 193, 4, 1.0, 10000),
    (32, 193, 8, 1.0, 3000),
    (32, 7681, 8, 0.25, 800),
]

def main():
    results = []
    grand = 0
    for (n, p, t, scale, nrand) in CONFIGS:
        cfg, famcount, L, dt = run_config(n, p, t, scale, nrand)
        results.append((cfg, famcount, L, dt))
        grand += sum(famcount.values())
        print(f"[done] n={n} p={p} t={t}  samples={sum(famcount.values())}  ({dt:.1f}s)")
    print(f"\nTOTAL SAMPLES: {grand}\n")

    for cfg, famcount, L, dt in results:
        n, p, t = cfg
        print("=" * 100)
        print(f"CONFIG n={n} p={p} t={t}   (deg f <= {n - t}; min weight = t = {t};"
              f" depths 0..{L - 1})")
        print("  families: " + ", ".join(f"{k}:{v}" for k, v in sorted(famcount.items())))
        print(f"  TABLE A   depth | 2^l | cap=min(2^l,n-t+1) | MAX alive (w,fam) | "
              f"MIN branch-supp (w,fam) | ceil(t/2^l) | max tot-supp/w (fam)")
        for ell in range(L):
            two = 1 << ell
            cap = min(two, n - t + 1)
            A, wA, famA = MAXALIVE[(cfg, ell)]
            ms, wm, famm = MINBSUPP[(cfg, ell)]
            tt, ww, famt = TOTRATIO[(cfg, ell)]
            wm_ex = WINMINEX.get((cfg, ell), None)
            print(f"    l={ell}:  {two:4d}  {cap:4d}   maxA={A:3d} (w={wA},{famA})"
                  f"   minsupp={ms} (w={wm},{famm})   ceil={-(-t // two)}"
                  f"   totmax={tt}/{ww}={tt / ww:.2f} ({famt})"
                  f"   min(supp-run)={wm_ex}")
        print("  TABLE B   minimal family (w = t exactly): alive histogram per depth")
        for ell in range(L):
            h = MINIMAL_HIST.get((cfg, ell))
            if h:
                print(f"    l={ell}: " + "  ".join(f"A={a}:{c}" for a, c in sorted(h.items())))
        print("  TABLE B'  random dense family: alive histogram per depth")
        for ell in range(L):
            h = RANDOM_HIST.get((cfg, ell))
            if h:
                print(f"    l={ell}: " + "  ".join(f"A={a}:{c}" for a, c in sorted(h.items())))
        print("  TABLE C   frontier: per depth, alive count A -> min weight w observed"
              " (family, zero-set coset-closure order d, bound B=ceil(t/2^l)*ceil(2^l/A))")
        for ell in range(L):
            two = 1 << ell
            row = []
            for A in range(1, two + 1):
                fr = FRONTIER.get((cfg, ell, A))
                if fr:
                    w, fam, d, _ = fr
                    B = (-(-t // two)) * (-(-two // A))
                    row.append(f"A={A}:w={w}(B={B},d={d},{fam[:6]})")
            print(f"    l={ell}: " + "  ".join(row))

    print("\n" + "=" * 100)
    print("WEIGHT-CONDITIONED DISTRIBUTION (showcase configs): w | count | minA..maxA per depth")
    for cfg in [(16, 97, 4), (32, 193, 4), (32, 193, 8)]:
        n, p, t = cfg
        L = n.bit_length() - 1
        ws = sorted({w for (c, ell, w) in DIST if c == cfg})
        print(f"  config n={n} p={p} t={t}:")
        for w in ws:
            cnt = DIST[(cfg, 0, w)][0]
            cells = []
            for ell in range(L):
                rec = DIST.get((cfg, ell, w))
                cells.append(f"l{ell}:{rec[1]}..{rec[2]}")
            print(f"    w={w:3d} (n={cnt:6d}): " + "  ".join(cells))

    print("\n" + "=" * 100)
    print("VIOLATION SUMMARY (expected: all zero except possibly H_frontier/H_task noted)")
    names = ['H_residue_alive', 'H_residue_supp', 'H_mono', 'H_pow2', 'H_frontier',
             'H_task', 'H_branch_floor', 'H_window', 'H_root_window', 'H_scaling']
    for name in names:
        c = VIOL.get(name, 0)
        line = f"  {name:20s}: {c} violations"
        if c and name in VIOL_EX:
            line += f"   first example: {VIOL_EX[name]}"
        print(line)
    # combinatorial cross-checks for (16,97,4) minimal family
    cfg = (16, 97, 4)
    if (cfg, 1) in MINIMAL_HIST:
        c1 = MINIMAL_HIST[(cfg, 1)].get(1, 0)
        c2 = MINIMAL_HIST[(cfg, 2)].get(1, 0)
        print(f"\nCROSS-CHECK (16,97,4) minimal family (1820 words):")
        print(f"  #words with alive(1)=1 = {c1}   (predicted C(8,6)=28: zero set closed under x->-x)")
        print(f"  #words with alive(2)=1 = {c2}   (predicted C(4,3)=4: zero set = union of 3 mu_4-cosets)")

if __name__ == '__main__':
    main()

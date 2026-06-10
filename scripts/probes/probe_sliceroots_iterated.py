#!/usr/bin/env python3
"""Adversarial probe for ITERATED slice root-coherence (O69 "Conjecture D in elementary
form" — the depth-l version of the weight/dead-locus tradeoff).

Claim under attack, depth l >= 1, domain mu_n in F_p (2^l | n so the tower stays
negation-closed for the first l levels):

  For ANY polynomial f (deg < n) with evaluation weight w = #{x in mu_n : f(x) != 0},
  the LIVE set at depth l
      live(l) = { y in mu_{n/2^l} : some depth-l branch value of f|mu_n is nonzero at y }
  satisfies  |live(l)| <= w.   Equivalently the DEAD locus — points where ALL 2^l
  branch values (= all 2^l iterated coefficient slices, by the slice law) vanish
  simultaneously — has size >= n/2^l - w: the alive slices share that common root set.

Also checked (the bridge the Lean proof uses):
  SLICE LAW (iterated): branchVal(b) agrees on mu_{n/2^|b|} with the evaluation of the
  iterated coefficient slice branchSlice(f, b), where
      branchSlice(f, [])        = f
      branchSlice(f, false::bs) = evenSlice(branchSlice(f, bs))    (coeff e -> e/2, x2)
      branchSlice(f, true ::bs) = X * oddSlice(branchSlice(f, bs)) (coeff e -> (e+1)/2, x2)

Adversarial families (not just random): minimal-weight vanishing-set words, fiber/coset
aligned supports (full depth-j fibers, so 2^j | n-w — the alive(l)=1 boundary of O69 C3),
multiplicative-coset supports, single-residue-class sparse coefficients, plus random.

Exit 1 on any violation; prints census totals and tightness stats.
"""
import random
import sys

random.seed(232)

VIOLATIONS = []
SLICE_LAW_FAILS = []
TOTAL = 0
TIGHT = 0          # live == min(w, n/2^l)
SLACK = 0          # live <  min(w, n/2^l)
ALIVE1_CASES = 0   # cases with exactly one alive branch (boundary structure)


def find_root_of_unity(p, n):
    # multiplicative generator of F_p^*, then power up
    for cand in range(2, p):
        ok = True
        q = p - 1
        # check cand is a generator (p small, factor q crudely)
        fs = set()
        m = q
        d = 2
        while d * d <= m:
            while m % d == 0:
                fs.add(d)
                m //= d
            d += 1
        if m > 1:
            fs.add(m)
        for f in fs:
            if pow(cand, q // f, p) == 1:
                ok = False
                break
        if ok:
            return pow(cand, (p - 1) // n, p)
    raise RuntimeError("no generator")


def poly_eval(f, x, p):
    acc = 0
    for c in reversed(f):
        acc = (acc * x + c) % p
    return acc


def even_slice(f, p):
    # evenSlice = contract 2 (f + f(-X)): coeff j -> 2*f[2j]
    return [(2 * f[2 * j]) % p for j in range((len(f) + 1) // 2)]


def x_odd_slice(f, p):
    # X * oddSlice: coeff 0 -> 0, coeff j+1 -> 2*f[2j+1]
    out = [0]
    j = 0
    while 2 * j + 1 < len(f):
        out.append((2 * f[2 * j + 1]) % p)
        j += 1
    return out


def trim(f):
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def branch_tree_vals(mu, v, depth, p):
    """levels[l] = list of (word, dict y->value incl zeros, support_set) at depth l."""
    cur = [((), dict(v))]
    doms = [sorted(set(v.keys()))]
    for l in range(depth):
        dom = doms[-1]
        newdom = sorted(set(pow(x, 2, p) for x in dom))
        fibers = {y: [x for x in dom if pow(x, 2, p) == y] for y in newdom}
        nxt = []
        for word, vb in cur:
            fe, fo = {}, {}
            for y in newdom:
                fe[y] = sum(vb[x] for x in fibers[y]) % p
                fo[y] = sum(vb[x] * x for x in fibers[y]) % p
            # words append in application order (Lean's list prepends; same tree).
            nxt.append((word + (0,), fe))
            nxt.append((word + (1,), fo))
        cur = nxt
        doms.append(newdom)
    return cur, doms


def branch_slices(f, depth, p):
    """list of (word, slicepoly) at depth `depth`, same word order as branch_tree_vals."""
    cur = [((), list(f))]
    for _ in range(depth):
        nxt = []
        for word, g in cur:
            nxt.append((word + (0,), trim(even_slice(g, p))))
            nxt.append((word + (1,), trim(x_odd_slice(g, p))))
        cur = nxt
    return cur


def poly_from_vanishing_set(A, p):
    # f = prod (X - a), a in A
    f = [1]
    for a in A:
        nf = [0] * (len(f) + 1)
        for i, c in enumerate(f):
            nf[i + 1] = (nf[i + 1] + c) % p
            nf[i] = (nf[i] - c * a) % p
        f = nf
    return f


def run_case(tag, p, mu, f, n, maxdepth):
    global TOTAL, TIGHT, SLACK, ALIVE1_CASES
    v = {x: poly_eval(f, x, p) for x in mu}
    w = sum(1 for x in mu if v[x] != 0)
    vals, doms = branch_tree_vals(mu, v, maxdepth, p)
    # group by depth: rebuild per-depth from scratch (cheap at these sizes)
    for l in range(1, maxdepth + 1):
        vals_l, doms_l = branch_tree_vals(mu, v, l, p)
        dom = doms_l[-1]
        slices = branch_slices(f, l, p)
        sl = {word: g for word, g in slices}
        live = set()
        alive_words = set()
        for word, vb in vals_l:
            g = sl[word]
            for y in dom:
                ge = poly_eval(g, y, p)
                if ge != vb[y]:
                    SLICE_LAW_FAILS.append((tag, p, n, l, word, y))
                if vb[y] != 0:
                    live.add(y)
                    alive_words.add(word)
        TOTAL += 1
        if len(alive_words) == 1:
            ALIVE1_CASES += 1
        bound = w
        if len(live) > bound:
            VIOLATIONS.append((tag, p, n, l, w, len(live), f))
        cap = min(w, n // (2 ** l))
        if len(live) == cap:
            TIGHT += 1
        elif len(live) < cap:
            SLACK += 1


def main():
    configs = [(17, 16), (97, 16), (97, 32), (193, 64), (257, 16), (257, 32), (769, 256)]
    for p, n in configs:
        g = find_root_of_unity(p, n)
        mu = [pow(g, i, p) for i in range(n)]
        assert len(set(mu)) == n and 0 not in mu
        v2 = (n & -n).bit_length() - 1
        maxdepth = min(3, v2)

        # family 1: minimal/small-weight vanishing-set words, random supports
        for w in sorted(set([1, 2, 3, n // 8, n // 8 + 1, n // 4 - 1, n // 4, n // 2 - 1])):
            if w < 1 or w >= n:
                continue
            for _ in range(6):
                Z = random.sample(mu, n - w)  # vanishing set, weight exactly w
                f = poly_from_vanishing_set(Z, p)
                run_case("vanish-rand", p, mu, f, n, maxdepth)

        # family 2: fiber-aligned vanishing sets (full depth-j fibers survive/vanish)
        for j in range(1, maxdepth + 1):
            img = sorted(set(pow(x, 2 ** j, p) for x in mu))
            for keep in [1, 2, len(img) // 2, len(img) - 1]:
                if keep < 1 or keep > len(img):
                    continue
                kept = set(random.sample(img, keep))
                Z = [x for x in mu if pow(x, 2 ** j, p) not in kept]  # vanish off kept fibers
                if not 0 < len(Z) < n:
                    continue
                f = poly_from_vanishing_set(Z, p)
                run_case(f"fiber-j{j}", p, mu, f, n, maxdepth)

        # family 3: multiplicative-coset supports (support = c * mu_d)
        for d in [2, 4, 8]:
            if n % d != 0:
                continue
            sub = [pow(g, i * (n // d), p) for i in range(d)]
            c = random.choice(mu)
            Z = [x for x in mu if x not in set(cc * c % p for cc in sub)]
            f = poly_from_vanishing_set(Z, p)
            run_case(f"coset-d{d}", p, mu, f, n, maxdepth)

        # family 4: single-residue-class sparse coefficients (one alive slice by design)
        for l in range(1, maxdepth + 1):
            for r in range(min(2 ** l, 4)):
                f = [0] * n
                exps = [e for e in range(n) if e % (2 ** l) == r]
                for e in random.sample(exps, min(3, len(exps))):
                    f[e] = random.randrange(1, p)
                run_case(f"sparse-l{l}r{r}", p, mu, trim(f), n, maxdepth)

        # family 5: fully random polynomials, varied degree
        for _ in range(10):
            deg = random.randrange(1, n)
            f = [random.randrange(p) for _ in range(deg)] + [random.randrange(1, p)]
            run_case("random", p, mu, f, n, maxdepth)

    print(f"cases (per-depth): {TOTAL}")
    print(f"slice-law mismatches: {len(SLICE_LAW_FAILS)}")
    print(f"live<=w violations: {len(VIOLATIONS)}")
    print(f"tight (live == min(w, n/2^l)): {TIGHT}   slack: {SLACK}")
    print(f"single-alive-branch cases: {ALIVE1_CASES}")
    for vio in VIOLATIONS[:5]:
        print("VIOLATION:", vio[:6])
    for sf in SLICE_LAW_FAILS[:5]:
        print("SLICE-LAW FAIL:", sf)
    if VIOLATIONS or SLICE_LAW_FAILS:
        sys.exit(1)
    print("ALL PASS")


if __name__ == "__main__":
    main()

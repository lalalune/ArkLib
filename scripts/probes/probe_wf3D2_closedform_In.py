#!/usr/bin/env python3
"""
wf-D2 (#444): CLOSED FORM hunt for the binding monomial far-line incidence I(n) and s*, delta*.

Object (FarCosetExplosion, axiom-clean per-witness <=1 gamma):
  far direction u1 = x^b (b not in RS[k] on a witness-sized set), offset u0 = x^a.
  For witness set R of size s, the condition  P_R(u0) + gamma P_R(u1) = 0  (P_R left-null of
  Vandermonde_R, codim s-k) is affine in gamma -> at most one gamma per FAR R.
  I(a,b;s) = #{ distinct gamma : EXISTS R, |R|=s, far, u0+gamma u1 in RS[R,k] }.
  delta* = sup{ r/n : max over far (a,b) of I(a,b; n-r) <= budget n }, s* = n-r* (binding size).

Goal: dump the EXACT distinct-gamma incidence at the binding direction for n=8,16,32 (and the
gamma multiset / structure) to read off the closed form, then s*(n), delta*(n) vs floor 1-rho-c/log n.

Vectorized: precompute all left-null vectors once per (n,p,s); each direction is fast linear algebra.
p-independence is checked across multiple primes.
"""
import sys, itertools, math
sys.path.insert(0, 'scripts/probes')
import numpy as np
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W


def left_null_rows(V, p):
    """All left-null rows of V (m x k) over F_p, as a list of length-m vectors."""
    m = len(V); k = len(V[0]) if m else 0
    aug = [list(V[i]) + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    rows = [r[:] for r in aug]; nc = k + m; pr = 0
    for c in range(k):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    out = []
    for row in rows:
        if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:]):
            out.append([row[k + j] % p for j in range(m)])
    return out


def precompute(S, p, k, s):
    """list of (R, P) where P is list of left-null rows (codim s-k)."""
    n = len(S); res = []
    for R in itertools.combinations(range(n), s):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null_rows(V, p)
        if P:
            res.append((R, P))
    return res


def incidence(u0, u1, nulls, p, return_gammas=False):
    good = {}
    for R, P in nulls:
        sz = len(R)
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return (p, None) if return_gammas else p
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good[g] = good.get(g, 0) + 1
    if return_gammas:
        return len(good), good
    return len(good)


def mono(b, S, p):
    return [pow(int(x), b, p) for x in S]


def binding_at_size(n, k, s, p):
    """max far-monomial incidence at witness size s; returns (maxI, best_dir, gammas_at_best)."""
    S = list(get_W(n, p).S)
    nulls = precompute(S, p, k, s)
    best = (-1, None, None)
    # far monomial direction: b in [k, s) (b<s so x^b is far for size-s witness)
    for b in range(k, s):
        ub = mono(b, S, p)
        for a in range(n):
            if a == b: continue
            ua = mono(a, S, p)
            I, gammas = incidence(ua, ub, nulls, p, return_gammas=True)
            if p > I > best[0]:
                best = (I, (a, b), gammas)
    return best


def deltastar(n, k, primes, smin=None, smax=None):
    """Find s* (smallest size s with maxI > budget=n binding) -> delta* = (n - s*)/n... actually
    delta* = r*/n with r* = n - s_first_good_above? We follow the convention: scan s downward
    (size shrinks = radius grows); the LAST s with maxI<=n is s*, delta*=(n-s*)/n."""
    smax = smax or (n - 1)
    smin = smin or (k + 1)
    budget = n
    rows = []
    for s in range(smax, smin - 1, -1):
        per = []
        for p in primes:
            I, d, g = binding_at_size(n, k, s, p)
            per.append((I, d))
        Ivals = [x[0] for x in per]
        pind = len(set(Ivals)) == 1
        rows.append((s, n - s, per[0][0], per[0][1], pind, Ivals))
    return rows


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=16)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--smin', type=int, default=None)
    ap.add_argument('--smax', type=int, default=None)
    ap.add_argument('--primes', type=str, default='200003,5000011,16777259')
    ap.add_argument('--dump', action='store_true', help='dump gamma multiset at binding')
    args = ap.parse_args()
    primes = [find_prime_cong1(args.n, int(x)) for x in args.primes.split(',')]
    print(f"n={args.n} k={args.k} rho={args.k/args.n:.4f} budget={args.n} primes={primes}", flush=True)
    print(f"{'s':>3} {'r=n-s':>5} {'maxI':>6} {'dir(a,b)':>10} {'p-indep':>8} {'Ivals'}", flush=True)
    rows = deltastar(args.n, args.k, primes, args.smin, args.smax)
    # rows are sorted s descending (r ascending). The binding s* = SMALLEST good size
    # (deepest good radius). I_bind = incidence at the first bad size below s*.
    smallest_good = None; Ibind = None; sbad = None
    for (s, r, I, d, pind, Iv) in rows:
        print(f"{s:>3} {r:>5} {I:>6} {str(d):>10} {str(pind):>8} {Iv}", flush=True)
    for (s, r, I, d, pind, Iv) in rows:  # descending s
        if I <= args.n:
            smallest_good = (s, r)
        else:
            if smallest_good is not None and sbad is None:
                Ibind = I; sbad = s
    if smallest_good:
        s_star, r_star = smallest_good
        print(f"\n*** binding: s*={s_star} (smallest good size), r*={r_star}, "
              f"delta* = r*/n = {r_star}/{args.n} = {r_star/args.n:.4f}", flush=True)
        if Ibind is not None:
            print(f"    I(n) = incidence at first bad size s={sbad}: {Ibind}", flush=True)
    # closed-form report at the WORST (binding-adjacent) size
    if args.dump:
        # dump gamma structure at the smallest size in range (deepest radius)
        smax = args.smax or (args.n - 1)
        s0 = (args.smin or (args.k + 1))
        I, d, g = binding_at_size(args.n, args.k, s0, primes[0])
        print(f"\n[dump] size s={s0} dir={d} I={I}", flush=True)
        if g:
            mults = sorted(g.values(), reverse=True)
            from collections import Counter
            print(f"  gamma multiplicity histogram: {dict(Counter(mults))}", flush=True)
    print("DONE", flush=True)

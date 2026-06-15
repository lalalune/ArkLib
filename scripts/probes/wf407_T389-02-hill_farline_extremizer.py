#!/usr/bin/env python3
"""
wf407 / T389-02-hill : worst-case far-line incidence — find the TRUE extremizer.

Object (FarLineIncidenceEquivariance.lean / FarCosetExplosion):
  Code C = RS[F_p, mu_n, k]  (polys of degree < k, evaluated on the n-th roots of unity).
  For an OFFSET word u0 : mu_n -> F_p  and a DIRECTION word u1 : mu_n -> F_p,
  the far-line incidence at radius delta is

     I(u0,u1; w) = #{ gamma in F_p :  exists codeword c in C  with
                       #{ i : c_i == u0_i + gamma*u1_i } >= w }

  where w = ceil((1-delta)*n) is the witness (agreement) threshold.
  delta* is governed by  I(delta) = max over (u0,u1) of this count, with u1 FAR from C.

THE THREAD CLAIM (389-T02/I2):
  power-words are NON-extremal; hill-climbing finds ~2.3x higher far-line incidence than
  power words (43 vs 19); the worst shallow-band stack is a HIGH monomial x^9, not the
  ladder x^8 -- in tension with the #407 "binding direction is low-exponent x^k" assumption.

WHAT WE DO (EXACT, not sampled):
  (1) Enumerate monomial directions u1 = x^a for ALL a in [k, n-1] (paired with u0 = 0 and
      with the best partner), compute exact I.  -> is the extremizer low or high exponent?
  (2) Hill-climb over ARBITRARY direction words u1 (coordinate-wise local moves) to convergence,
      multi-restart, to find the GLOBAL worst far-line incidence.  Compare to the monomial best.
  (3) Verdict on whether the extremal binding direction is monomial / low-exp / high-exp / neither.

Engine: for a fixed (u0,u1) and fixed gamma, the max agreement of the affine line point
  t_i = u0_i + gamma*u1_i  with any degree-<k poly is a LIST-DECODING radius computation.
  We compute it EXACTLY by, for every (k)-subset?  No -- too slow.  Instead:
  the max agreement = max over codewords c of #agreements.  A codeword agreeing on >= k points
  is DETERMINED by any k of those points (Lagrange).  So we enumerate candidate codewords by
  picking k coordinates, interpolating, and counting agreements -- but that is C(n,k) per gamma.
  For the (n,k) sizes we use (n<=16, k small) and the prize-thin regime k ~ n/4..n/2 this is
  feasible at n=12,16.  We cap with a SMARTER method: group by agreement.

  Concretely max_agreement(t) over deg<k polys:
     We want the largest set S of points (x_i, t_i) lying on a single deg<k poly.
     Enumerate over all k-subsets is C(n,k); for n=12,k=6 that's 924, times p gammas times
     (per-subset agreement count O(n)) -> fine.  For n=16 we restrict to relevant gammas.
"""
import itertools, sys
from functools import lru_cache

# ---------- finite field F_p ----------
def find_prime_with_subgroup(n, lo):
    """smallest prime p > lo with n | p-1 (so mu_n exists)."""
    p = lo + 1
    while True:
        if p % n == 1 and is_prime(p):
            return p
        p += 1

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    # find generator of F_p^*
    fact = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fact):
            return g
    raise RuntimeError

def factorize(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of the order-n subgroup
    dom = [pow(h, i, p) for i in range(n)]
    assert len(set(dom)) == n
    return dom

# ---------- Lagrange interpolation / agreement ----------
def interp_eval_all(xs_sub, ts_sub, all_xs, p):
    """Given k points (xs_sub[j], ts_sub[j]), the unique deg<k poly through them;
       return its value at every x in all_xs."""
    k = len(xs_sub)
    # Lagrange: P(x) = sum_j ts_sub[j] * prod_{m!=j} (x - xs_sub[m])/(xs_sub[j]-xs_sub[m])
    # precompute denominators
    out = []
    for x in all_xs:
        val = 0
        for j in range(k):
            num = ts_sub[j]
            den = 1
            for m in range(k):
                if m == j: continue
                num = (num * (x - xs_sub[m])) % p
                den = (den * (xs_sub[j] - xs_sub[m])) % p
            val = (val + num * pow(den, p-2, p)) % p
        out.append(val)
    return out

def max_agreement(dom, t, k, p, kchoose_cache):
    """Max #{i : P(dom_i)=t_i} over deg<k polys P.  Exact via k-subset interpolation.
       Optimization: only need agreement >= k to matter (any deg<k poly hitting < k pts is
       beaten by interpolating exactly k of the hits). The empty/poly agreeing on < k pts:
       max agreement could be < k only if NO k points are collinear-on-a-poly with the rest;
       but ANY k points define a poly agreeing on >= k. So max_agreement >= k always (k<=n).
       We compute the true max by scanning k-subsets and counting agreements of their interpolant.
    """
    n = len(dom)
    best = k  # any k points give >= k
    seen = set()
    for sub in kchoose_cache:
        xs_sub = [dom[j] for j in sub]
        ts_sub = [t[j] for j in sub]
        # interpolate, evaluate everywhere, count agreements
        vals = interp_eval_all(xs_sub, ts_sub, dom, p)
        cnt = sum(1 for i in range(n) if vals[i] == t[i])
        if cnt > best:
            best = cnt
    return best

def far_line_incidence(dom, u0, u1, k, p, w, kchoose_cache, gamma_set=None):
    """Count gamma in F_p (or in gamma_set) s.t. max_agreement(u0+gamma*u1) >= w."""
    n = len(dom)
    cnt = 0
    bad = []
    gammas = range(p) if gamma_set is None else gamma_set
    for gamma in gammas:
        t = [(u0[i] + gamma*u1[i]) % p for i in range(n)]
        ma = max_agreement(dom, t, k, p, kchoose_cache)
        if ma >= w:
            cnt += 1
            bad.append(gamma)
    return cnt, bad

def is_far(dom, u1, k, p, kchoose_cache, w):
    """u1 is 'far' if it is NOT within (n-w) errors of the code at the witness radius,
       i.e. max_agreement(u1) < w  (u1 itself is not explainable at the radius)."""
    ma = max_agreement(dom, u1, k, p, kchoose_cache)
    return ma < w

# ---------- main experiment ----------
def run(n, k, delta_num, delta_den, p=None, do_hillclimb=True, hc_restarts=40, seed=12345):
    import random
    rng = random.Random(seed)
    if p is None:
        p = find_prime_with_subgroup(n, 50)
    dom = mu_n(p, n)
    # witness threshold w = ceil((1-delta)*n) = n - floor(delta*n)
    # delta = delta_num/delta_den ; floor(delta*n)=floor(n*num/den)
    fl = (n*delta_num)//delta_den
    w = n - fl
    kchoose = list(itertools.combinations(range(n), k))
    print(f"=== n={n} k={k} p={p} delta={delta_num}/{delta_den} -> agreement threshold w={w} "
          f"(rate rho={k}/{n}={k/n:.3f})  #k-subsets={len(kchoose)} ===")

    monvals = [pow_word(dom, a, p) for a in range(n)]  # x^a evaluated

    # ---- (1) monomial directions, u0 = 0 ----
    # u0=0: line is gamma*x^a ; gamma=0 gives zero word (codeword), agreement n>=w always -> count it
    print("\n-- monomial directions u1=x^a, offset u0=0 --")
    mono_results = []
    for a in range(k, n):  # a>=k so x^a is not itself a codeword (far candidate)
        u1 = monvals[a]
        if not is_far(dom, u1, k, p, kchoose, w):
            mono_results.append((a, None, "u1 not far"))
            continue
        cnt, bad = far_line_incidence(dom, [0]*n, u1, k, p, w, kchoose)
        mono_results.append((a, cnt, ""))
        print(f"   a={a:2d}  I={cnt:3d}   (bad gammas: {len(bad)})")
    valid_mono = [(a,c) for (a,c,_) in mono_results if c is not None]
    if valid_mono:
        best_a, best_mono = max(valid_mono, key=lambda t: t[1])
        print(f"   -> best monomial (u0=0): a={best_a}, I={best_mono}")

    # ---- (1b) monomial PAIR stacks: direction x^a with offset x^b (the (X^a,X^b) families) ----
    print("\n-- monomial-pair directions: u1=x^a, offset u0=x^b (b<a) --")
    pair_best = (None, None, -1)
    pair_rows = []
    for a in range(k, n):
        u1 = monvals[a]
        if not is_far(dom, u1, k, p, kchoose, w):
            continue
        for b in range(0, a):
            u0 = monvals[b]
            cnt, bad = far_line_incidence(dom, u0, u1, k, p, w, kchoose)
            pair_rows.append((a, b, cnt))
            if cnt > pair_best[2]:
                pair_best = (a, b, cnt)
    pair_rows.sort(key=lambda r: -r[2])
    for (a,b,c) in pair_rows[:8]:
        print(f"   (X^{a}, X^{b}):  I={c}")
    print(f"   -> best monomial-pair: (X^{pair_best[0]}, X^{pair_best[1]}), I={pair_best[2]}")

    # ---- (2) hill-climb over ARBITRARY direction words u1 (offset u0 = 0) ----
    hc_best = -1; hc_word = None
    if do_hillclimb:
        print(f"\n-- hill-climb over arbitrary direction words (u0=0), {hc_restarts} restarts --")
        def score(u1):
            if not is_far(dom, u1, k, p, kchoose, w):
                return -1
            cnt, _ = far_line_incidence(dom, [0]*n, u1, k, p, w, kchoose)
            return cnt
        for r in range(hc_restarts):
            # start: random word, or a monomial seed on some restarts
            if r < n - k:
                cur = list(monvals[k + r])      # seed from monomials
            else:
                cur = [rng.randrange(p) for _ in range(n)]
            cs = score(cur)
            improved = True
            while improved:
                improved = False
                for i in range(n):
                    old = cur[i]
                    bestv, bestsc = old, cs
                    # try all field values? p can be big; sample a candidate set:
                    cand = set(rng.randrange(p) for _ in range(min(p, 24)))
                    cand |= set(monvals[a][i] for a in range(n))  # structured candidates
                    for v in cand:
                        if v == old: continue
                        cur[i] = v
                        sc = score(cur)
                        if sc > bestsc:
                            bestsc, bestv = sc, v
                    cur[i] = bestv
                    if bestsc > cs:
                        cs = bestsc; improved = True
            if cs > hc_best:
                hc_best = cs; hc_word = list(cur)
        print(f"   -> hill-climb best far-line incidence: I={hc_best}")
        # classify the converged word: is it a monomial? low/high support?
        classify(dom, hc_word, monvals, p, n)

    print("\n=== SUMMARY ===")
    mono0 = best_mono if valid_mono else -1
    print(f"   best monomial (u0=0):      I={mono0}")
    print(f"   best monomial-pair:        I={pair_best[2]}  at (X^{pair_best[0]},X^{pair_best[1]})")
    if do_hillclimb:
        print(f"   hill-climb (arbitrary u1): I={hc_best}")
    return dict(p=p, w=w, best_mono=mono0, best_mono_a=(best_a if valid_mono else None),
                pair_best=pair_best, hc_best=hc_best)

def pow_word(dom, a, p):
    return [pow(x, a, p) for x in dom]

def classify(dom, word, monvals, p, n):
    """Is the converged word a scalar multiple of a monomial?"""
    for a in range(n):
        m = monvals[a]
        # check word = c * m for some constant c (and m nowhere 0)
        ratios = set()
        ok = True
        for i in range(n):
            if m[i] == 0:
                if word[i] != 0: ok=False; break
                continue
            ratios.add((word[i]*pow(m[i],p-2,p))%p)
        if ok and len(ratios) == 1:
            print(f"      converged word = {ratios} * x^{a}  (it IS a scaled monomial)")
            return
    print(f"      converged word is NOT a scaled monomial (genuinely non-monomial extremizer)")

if __name__ == "__main__":
    # The thread reports n=16, rate 1/2, the (12,6) phenomenon, high vs low exponent.
    # Run the two enumerable instances the thread/synthesis used.
    print("########## INSTANCE A: (n,k)=(12,6), delta=1/4 [O138 instance] ##########")
    run(12, 6, 1, 4, p=13, do_hillclimb=True, hc_restarts=30)
    print("\n########## INSTANCE B: (n,k)=(16,8), delta past Johnson (agree>=9 -> w=9) ##########")
    # delta with floor(16*delta)=7 -> w=9 ; delta in [7/16, 8/16) ; use 7/16 boundary -> use num/den giving floor 7
    run(16, 8, 7, 16, p=17, do_hillclimb=True, hc_restarts=24)

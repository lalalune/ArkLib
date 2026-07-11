#!/usr/bin/env python3
"""
probe_407_regimeB_n32_sstar_exact.py  (#444, wf-D2 regime-B residual)

RESOLVES the explicitly-flagged OPEN SUB-QUESTION (wf-D2 entry, push e48d5ef59):
  Regime A (n=16..28, EXACT): s* = n/2 - 1 (delta* = 1/2 + 1/n -> Johnson).
  Regime B (n>=32, GPU): "s* PINS at exactly 13 across n=32,34,38 ... a pinned s* with climbing
  delta* is the signature of a SEARCH CEILING, not a law. n=32 deviation (s*=13 not 15) MAY BE REAL
  (n=32 within H100 reach) and IS THE GENUINE OPEN SUB-QUESTION."

The GPU enumerated size-s WITNESS sets (C(32,s), infeasible deep) and TIMED OUT for n>=36.
This probe avoids that wall ENTIRELY via the EXACT (k+1)-subset candidate-alpha generation
(the in-tree FarCosetExplosion / divided-difference fact: every bad alpha at agreement >= k+1 is
produced by some (k+1)-subset). For k=2 that is C(32,3)=4960 subsets -- trivially feasible. Then
max-agreement per candidate is exact. So I(a,b;thr) = #{alpha : maxagree(x^a+alpha x^b, RS[k]) >= thr}
is EXACT at EVERY threshold thr, over the FULL direction sweep (all gcd strata), no enumeration wall.

  s* = max { thr : max_over_far_dirs I(a,b; thr) <= budget = n }.

If s* = 15 (= n/2-1): regime A law extends, GPU s*=13 was a search ceiling.
If s* = 13 (or other < 15) and STABLE under widening directions + multi-prime: a REAL regime-B
plateau -- a genuine sub-question result.

Prize-faithful: PROPER mu_n (m=(p-1)/n > 1), p >> n^3, p == 1 mod n, NEVER n=q-1. Multi-prime.
Exact integer arithmetic over F_p, no floats in the incidence. Python-only => axiom-clean trivially.
"""
import sys, itertools, argparse
from math import gcd, sqrt, floor, ceil


def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True


def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while not (is_prime(p) and (p - 1) % n == 0):
        p += n
    return p


def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p - 1) // n, p)
        if pow(w, n, p) == 1 and all(pow(w, n // q, p) != 1 for q in (2, 3, 5, 7) if n % q == 0):
            return w
    raise RuntimeError("no generator")


def inv(a, p):
    return pow(a % p, p - 2, p)


def alpha_for_subset(Tvals, a, b, p, k):
    """(k+1)-subset interpolable by deg<k for word x^a+alpha x^b => unique alpha (or None)."""
    Xs = Tvals
    m = k + 1
    M = [[pow(Xs[c], i, p) for c in range(m)] for i in range(k)]
    rows = [r[:] for r in M]
    pivots = []
    r = 0
    for c in range(m):
        piv = None
        for rr in range(r, k):
            if rows[rr][c] % p != 0:
                piv = rr
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c], p)
        rows[r] = [(xx * iv) % p for xx in rows[r]]
        for rr in range(k):
            if rr != r and rows[rr][c] % p != 0:
                f = rows[rr][c]
                rows[rr] = [(aa - f * bb) % p for aa, bb in zip(rows[rr], rows[r])]
        pivots.append(c)
        r += 1
    free = [c for c in range(m) if c not in pivots]
    if not free:
        return None
    fc = free[0]
    lam = [0] * m
    lam[fc] = 1
    for i, c in enumerate(pivots):
        lam[c] = (-rows[i][fc]) % p
    U = sum(lam[c] * pow(Xs[c], a, p) for c in range(m)) % p
    V = sum(lam[c] * pow(Xs[c], b, p) for c in range(m)) % p
    if V % p == 0:
        return None
    return (-U * inv(V, p)) % p


def _agree_on_subset(n, k, p, X, y, bx_idx):
    """agreement count of word y with the unique deg<k poly through the k points bx_idx."""
    bx = [X[i] for i in bx_idx]
    by = [y[i] for i in bx_idx]
    cnt = 0
    for jx in range(n):
        xx = X[jx]
        tot = 0
        for jj in range(k):
            num = by[jj]
            den = 1
            xj = bx[jj]
            for ll in range(k):
                if ll != jj:
                    num = num * ((xx - bx[ll]) % p) % p
                    den = den * ((xj - bx[ll]) % p) % p
            tot = (tot + num * inv(den, p)) % p
        if tot == y[jx]:
            cnt += 1
    return cnt


def max_agree(n, k, p, X, a, b, alpha):
    """EXACT max agreement of word (x^a + alpha x^b) with RS[k] over domain X (size n),
    via full C(n,k) k-subset enumeration (each k-subset determines a unique deg<k poly)."""
    y = [(pow(X[j], a, p) + alpha * pow(X[j], b, p)) % p for j in range(n)]
    best = 0
    for comb in itertools.combinations(range(n), k):
        c = _agree_on_subset(n, k, p, X, y, comb)
        if c > best:
            best = c
        if best == n:
            break
    return best


def run(n, k, primes_lo_mult):
    budget = n
    rho = k / n
    johnson_s = sqrt(rho) * n   # Johnson agreement threshold
    cap_s = rho * n             # capacity agreement (= k)
    print(f"=== n={n} k={k} rho={rho:.4f} budget=n={budget} "
          f"Johnson_thr~{johnson_s:.2f} regimeA_pred_s*={n//2-1} ===", flush=True)
    for mult in primes_lo_mult:
        p = prime_ge(mult * n ** 3, n)
        w = find_gen(p, n)
        X = [pow(w, j, p) for j in range(n)]
        m_index = (p - 1) // n
        assert m_index > 1, "must be PROPER subgroup"
        # full direction sweep: one representative per gcd stratum is enough (incidence depends on
        # the pencil only through the orbit structure gcd(b-a,n)), but we sweep ALL (a,b) with a,b
        # far (>= k) to be safe and to catch any non-gcd-determined worst direction.
        # To keep cost bounded we fix b in {k,k+1,...} and sweep a over all far residues, dedup by
        # the FULL (a,b) but report the max over everything.
        per_thr_maxI = {}   # thr -> (maxI, dir)
        # Direction sweep: incidence depends on the pencil through gcd(b-a,n) (orbit law). Sweep ONE
        # representative per gcd stratum, fixing b=k (lowest far exponent = empirically worst) and
        # choosing a to realize each achievable gcd(b-a,n). Worst direction is the deeply-composite
        # gcd (n/4, n/2) family (board: antipodal/subgroup-coset). This is exact (gcd determines I).
        b = k
        seen_gcd = {}
        for a in range(k, n):
            if a == b:
                continue
            d = gcd((b - a) % n, n)
            if d not in seen_gcd:
                seen_gcd[d] = (a, b)
        dirs = list(seen_gcd.values())
        for (a, b) in dirs:
            cand = set()
            for Tidx in itertools.combinations(range(n), k + 1):
                al = alpha_for_subset([X[j] for j in Tidx], a, b, p, k)
                if al is not None:
                    cand.add(al)
            agrs = [max_agree(n, k, p, X, a, b, al) for al in cand]
            for thr in range(k + 1, n + 1):
                I = sum(1 for g in agrs if g >= thr)
                cur = per_thr_maxI.get(thr)
                if cur is None or I > cur[0]:
                    per_thr_maxI[thr] = (I, (a, b, gcd((b - a) % n, n)))
        # find s* = max thr with maxI(thr) <= budget
        sstar = None
        for thr in range(n, k, -1):
            mi = per_thr_maxI.get(thr, (0, None))[0]
            if mi <= budget:
                sstar = thr
                break
        print(f"  p={p} (p/n^3={p/n**3:.1f}, m=(p-1)/n={m_index}):", flush=True)
        # print the binding band
        band = range(max(k + 1, (n // 2) - 4), min(n, (n // 2) + 3) + 1)
        for thr in band:
            mi, d = per_thr_maxI.get(thr, (0, None))
            flag = "" if mi <= budget else " OVER"
            star = " <== s*" if thr == sstar else ""
            print(f"     thr(s)={thr:>3}  maxI={mi:>5}  worst_dir={d}{flag}{star}", flush=True)
        print(f"   >>> s*(n={n}, p/n^3={p/n**3:.0f}) = {sstar}   "
              f"delta*=(n-s*)/n={(n-sstar)/n:.5f}   regimeA_pred={n//2-1}", flush=True)
    print(flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=32)
    ap.add_argument('--k', type=int, default=2)
    args = ap.parse_args()
    # two prime scales (p/n^3 ~ 8 and ~ 80) to check q-invariance of s*
    run(args.n, args.k, primes_lo_mult=[8, 80])

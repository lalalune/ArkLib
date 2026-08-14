#!/usr/bin/env python3
"""
wf-D3 (#444) PINCH TEST: does the wf-NH over-determined incidence FLOOR meet the
KKH26 ceiling  delta* <= 1 - r/2^mu  ?

Two converging brackets on the SAME object delta* = sup{ delta : I(delta) <= q*eps* }:

  FLOOR  (wf-NH over-determined, p-INDEPENDENT combinatorial):
     For each witness size s (radius r = n - s), the WORST far-line incidence
     I(s) = max over far monomial directions (a,b), b in [0,size), of the exact
     FarCosetExplosion count (each witness contributes <=1 gamma => p-independent
     union count).  I decreases as s grows.  The binding size
         s* = min{ s > k : I(s) <= budget }      (budget = q*eps* = n)
     gives the OVER-DET FLOOR  delta*_floor = (n - s*)/n   (the largest delta whose
     worst over-det incidence is still within budget -- a LOWER witness on delta* via
     the bad family at radius just-above, i.e. s*-1 saturates; see note).

     NOTE on direction of the bracket: the over-det incidence count is the size of the
     BAD set at radius r = n - s.  I(s*-1) > budget => radius n-(s*-1) has a bad family
     exceeding budget => that radius is BAD => delta* <= (n-(s*-1))/n = (n-s*+1)/n is an
     UPPER fact; and I(s*) <= budget means radius n-s* is (for the monomial family) within
     budget.  So the over-det BINDING radius is delta_bind = (n - s*)/n, the transition.
     We report delta_bind and compare to the KKH26 ceiling.

  CEILING (KKH26 kkh26_mcaDeltaStar_le, in-tree axiom-clean):
     delta* <= 1 - r/2^mu   valid whenever  eps* < 2^r * C(2^{mu-1}, r) / p.
     2^mu = n (thin full subgroup).  Minimize 1 - r/n over r making the spread valid
     at eps* = 2^-128, p = q ~ n^beta  =>  tightest ceiling.

PINCH <=> delta_bind == delta_ceil (or |gap| -> 0).  We tabulate both, the gap, at
n in {16,32}, rho in {1/2,1/4,1/8,1/16}.  n=64 floor is C(64,s)-expensive; we do the
ceiling for all n and the floor where feasible.

EXACT integers throughout (budget, binomials, incidence).  p-independence of the floor
already established by wf-NH; we use ONE prime per (n,k) and (separately) re-verify
p-independence on the binding s only.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from math import comb, log2
from probe_farline_incidence_exact import find_prime_cong1, left_null
from prize_workspace import get_W

EPS_SHIFT = 128  # eps* = 2^-128


# ----------------------------------------------------------------- FLOOR (over-det incidence)
def precompute_nulls(S, p, k, size):
    n = len(S)
    nulls = []
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if P:
            nulls.append((R, P))
    return nulls


def inc_from_nulls(u0, u1, nulls, p):
    good = set()
    for R, P in nulls:
        sz = len(R)
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return p
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good.add(g)
    return len(good)


def mono(b, S, p):
    return [pow(int(x), b, p) for x in S]


def worst_far_incidence(n, k, size, S, p):
    """max over far monomial dirs (b in [0,size)) of the exact incidence at this size."""
    nulls = precompute_nulls(S, p, k, size)
    best = -1
    for b in range(size):
        for a in range(n):
            if a == b:
                continue
            I = inc_from_nulls(mono(a, S, p), mono(b, S, p), nulls, p)
            if p > I > best:
                best = I
    return best


def floor_bind(n, k, budget, S, p, smax=None):
    """Scan size up from k+1; return (s*, I(s*), I(s*-1)) where s* = min size with I<=budget.
    Returns delta_bind = (n - s*)/n."""
    smax = smax or n - 1
    prev = None  # (size, I)
    for size in range(k + 1, smax + 1):
        I = worst_far_incidence(n, k, size, S, p)
        if I <= budget:
            d = (n - size) / n
            return size, I, (prev[1] if prev else None), d
        prev = (size, I)
    return None, None, (prev[1] if prev else None), None


# ----------------------------------------------------------------- CEILING (KKH26)
def kkh26_ceiling(n, q):
    """tightest 1 - r/n over r with eps* < 2^r * C(n/2, r) / q.
    n = 2^mu, 2^{mu-1} = n//2.  Exact-integer:  q < 2^r * C(n/2,r) << 128 ... careful:
    eps* = 2^-128 < 2^r C(n/2,r)/q  <=>  q < 2^r * C(n/2,r) * 2^128."""
    half = n // 2
    best_r = None
    for r in range(1, half + 1):
        lhs = q
        rhs = (1 << r) * comb(half, r) << EPS_SHIFT
        if lhs < rhs:
            best_r = r  # smallest valid r -> largest 1-r/n ceiling? NO: we want tightest=smallest ceiling
            break
    if best_r is None:
        return None, None
    # tightest ceiling = LARGEST valid r (smallest 1 - r/n) -- all r>=best_r valid since rhs grows
    rmax = None
    for r in range(half, 0, -1):
        rhs = (1 << r) * comb(half, r) << EPS_SHIFT
        if q < rhs:
            rmax = r
            break
    d_ceil = 1 - rmax / n
    return rmax, d_ceil


RATES = [("1/2", 1, 2), ("1/4", 1, 4), ("1/8", 1, 8), ("1/16", 1, 16)]


def run():
    print("wf-D3 PINCH: over-det incidence FLOOR vs KKH26 ceiling 1 - r/n\n"
          "budget = q*eps* = n (prize).  q tested at n^4 (prize beta).\n")
    for n in [16, 32]:
        print(f"################  n = {n}  ################")
        for (rl, rn, rd) in RATES:
            k = n * rn // rd
            if k < 1:
                continue
            rho = k / n
            d_J = 1 - rho ** 0.5
            d_cap = 1 - rho
            q = n ** 4
            p = find_prime_cong1(n, q)
            S = list(get_W(n, p).S)
            budget = n  # q*eps* = n
            # floor: only feasible where C(n,size) manageable.  Cap the scan.
            smax = min(n - 1, k + 8) if n >= 32 else n - 1
            s_star, I_s, I_prev, d_bind = floor_bind(n, k, budget, S, p, smax=smax)
            rmax, d_ceil = kkh26_ceiling(n, q)
            print(f" rho={rl} k={k} (Johnson {d_J:.4f}, cap {d_cap:.4f}):")
            if s_star is not None:
                gap = d_ceil - d_bind
                pinch = "PINCH!" if abs(gap) < 1e-9 else f"gap={gap:+.4f}"
                inwin = (d_bind > d_J) and (d_bind < d_cap)
                print(f"   FLOOR over-det: s*={s_star} I(s*)={I_s}<=bud<{I_prev}=I(s*-1)"
                      f"  delta_bind=(n-{s_star})/n={d_bind:.4f}  {'IN-WINDOW' if inwin else 'out'}")
                print(f"   CEIL  KKH26:   r={rmax}  delta_ceil=1-{rmax}/{n}={d_ceil:.4f}   ==> {pinch}")
            else:
                print(f"   FLOOR over-det: no binding s in [k+1,{smax}] (I>budget throughout)  I(smax)={I_prev}")
                print(f"   CEIL  KKH26:   r={rmax}  delta_ceil={d_ceil:.4f}")
            print(flush=True)


if __name__ == '__main__':
    run()
    print("DONE")

#!/usr/bin/env python3
"""
probe_factorial_moments.py  (#389)

THE DECISIVE NUMERIC the fleet's 18-agent verification pass identified but never ran:
the t-th FACTORIAL MOMENT E[C(L,t)] of the list-size L of the REAL mu_n RS super-code,
compared to the Poisson / average-term prediction mu^t / t!.

WHY t=3 IS THE FIRST INFORMATIVE ORDER.
  L(s) = #{ c in C+ : d(c,s) <= w }, the radius-w list around a uniform center s in F_q^n.
  C+ = RS[mu_n, k+1]  (the deep super-code, dim k+1, MDS).
  Leading conjecture: delta* = H_q^{-1}(1 - rho - log_q(1/eps*)/n) = the AVERAGE / first-moment
  term.  It is the TRUE delta* IFF the worst-vs-average ratio R(n) = max_C+ |list|/E|list| is
  q^{o(n)} -- i.e. iff L concentrates, i.e. iff the factorial moments stay Poisson:
        E[C(L,t)] = mu^t / t!   for all t up to t ~ 1/eta.
  The 2nd moment is q-independent Poisson (fleet, proven). BUT every MDS code shares ONE weight
  enumerator A_omega, so t=2 = (function of A_omega) is BLIND to which MDS code -- it cannot see
  the mu_n-specific structure (the KKH26 2^Omega(1/eta) heavy line lives in the JOINT structure).
  The mu_n clustering can FIRST appear at t=3, governed by the BI-weight (joint) enumerator.
  So: compute E[C(L,3)] EXACTLY for the real mu_n super-code and compare to mu^3/6.
        ratio_t := E[C(L,t)] * t! / mu^t.   ratio=1 <=> Poisson (gate holds at order t);
        ratio>1 <=> a structured t-tuple cluster (the worst object the 2nd moment is blind to).

EXACT METHOD (no center enumeration; q^n is huge).
  E[C(L,t)] = (1/t!)(q^{k+1}/q^n) * S_t,
  S_t = sum over ordered (d_2..d_t) in (C+)^{t-1} with {0,d_2..d_t} all distinct, of
        Vol_cap(0,d_2,...,d_t) = #{ e in F_q^n : wt(e)<=w and wt(e-d_i)<=w for all i }.
  Translation s -> s - c_1 collapses the c_1 sum to a factor q^{k+1}; the d_i = c_i - c_1 are
  codewords of the linear super-code.  Vol_cap is computed by a per-coordinate DP over the joint
  (wt(e), wt(e-d_2), wt(e-d_3)) caps, whose transfer depends only on the COLUMN TYPE at each
  coordinate (the equality pattern among 0, d_2[j], d_3[j]).  5 column types -> histogram of size
  <= C(n+4,4) -> cheap cached DP.  Real mu_n structure enters through which (d_2,d_3) pairs occur.

This is honest, prize-regime-relevant, open-core-free new data.  decide-clean by construction.
"""

import sys
from itertools import product
from functools import lru_cache
import numpy as np


def field_mu_subgroup(q, n):
    """Return mu_n (the order-n multiplicative subgroup) of F_q as a sorted list, requires n|q-1."""
    assert (q - 1) % n == 0, f"need n|q-1: n={n}, q={q}"
    # find a generator g of F_q^*
    def order(x):
        o, y = 1, x % q
        while y != 1:
            y = (y * x) % q
            o += 1
        return o
    g = None
    for cand in range(2, q):
        if order(cand) == q - 1:
            g = cand
            break
    assert g is not None
    h = pow(g, (q - 1) // n, q)  # generator of mu_n
    sub = sorted({pow(h, i, q) for i in range(n)})
    assert len(sub) == n
    return sub


def supercode_codewords(q, n, dim, domain):
    """All codewords of RS[domain, dim] = evals of polys of degree < dim. Shape (q^dim, n)."""
    pts = np.array(domain, dtype=np.int64)
    rows = []
    for coeffs in product(range(q), repeat=dim):
        # poly c0 + c1 x + ... ; evaluate on domain mod q (Horner)
        val = np.zeros(n, dtype=np.int64)
        for c in reversed(coeffs):
            val = (val * pts + c) % q
        rows.append(val)
    return np.array(rows, dtype=np.int64)


def ball_volume(q, n, w):
    from math import comb
    return sum(comb(n, i) * (q - 1) ** i for i in range(0, w + 1))


# ---- Vol_cap via per-coordinate DP keyed by column-type histogram ----
# column types for pair (a,b)=(d2[j],d3[j]) relative to 0:
#   0: a==0,b==0          transfer: 1*(0,0,0), (q-1)*(1,1,1)
#   1: a==0,b!=0          1*(0,0,1), 1*(1,1,0), (q-2)*(1,1,1)
#   2: a!=0,b==0          1*(0,1,0), 1*(1,0,1), (q-2)*(1,1,1)
#   3: a!=0,b!=0,a==b     1*(0,1,1), 1*(1,0,0), (q-2)*(1,1,1)
#   4: a!=0,b!=0,a!=b     1*(0,1,1), 1*(1,0,1), 1*(1,1,0), (q-3)*(1,1,1)
def _type_transfers(q):
    return {
        0: [(1, (0, 0, 0)), (q - 1, (1, 1, 1))],
        1: [(1, (0, 0, 1)), (1, (1, 1, 0)), (q - 2, (1, 1, 1))],
        2: [(1, (0, 1, 0)), (1, (1, 0, 1)), (q - 2, (1, 1, 1))],
        3: [(1, (0, 1, 1)), (1, (1, 0, 0)), (q - 2, (1, 1, 1))],
        4: [(1, (0, 1, 1)), (1, (1, 0, 1)), (1, (1, 1, 0)), (q - 3, (1, 1, 1))],
    }


def vol_cap3_from_hist(hist, q, w):
    """Vol_cap(0,d2,d3) from column-type histogram hist=(n0,n1,n2,n3,n4). 3D capped DP."""
    transfers = _type_transfers(q)
    cap = w + 1  # states 0..w, w+1 = overflow (absorbing -> infeasible, dropped at end)
    # dp[x][y][z] = number of e-prefixes with partial weights (x,y,z), x,y,z in 0..w (drop overflow)
    dp = np.zeros((cap, cap, cap), dtype=object)
    dp[0, 0, 0] = 1
    for ttype, count in enumerate(hist):
        for _ in range(count):
            ndp = np.zeros((cap, cap, cap), dtype=object)
            for mult, (dx, dy, dz) in transfers[ttype]:
                # shift dp by (dx,dy,dz), drop anything that would exceed w
                xs = cap - dx
                ys = cap - dy
                zs = cap - dz
                if xs <= 0 or ys <= 0 or zs <= 0:
                    continue
                ndp[dx:dx + xs, dy:dy + ys, dz:dz + zs] += mult * dp[:xs, :ys, :zs]
            dp = ndp
    return int(dp.sum())


def vol_cap2(weight, q, n, w):
    """Vol_cap(0,d) depends only on wt(d)=weight. Use 3D DP with d3=0 columns => hist of types 0/2."""
    # coords with d=0 -> type 0 (a==0,b==0 since d3=0 too); coords with d!=0 -> a!=0,b==0 -> type 2.
    hist = (n - weight, 0, weight, 0, 0)
    return vol_cap3_from_hist(hist, q, w)


def run(q, n, k, domain, name, do_t3=True):
    dim = k + 1
    C = supercode_codewords(q, n, dim, domain)
    Ncw = C.shape[0]
    print(f"\n=== {name}: q={q} n={n} k={k} (super-code dim={dim}, |C+|={Ncw}) ===")
    # weight of each codeword
    wts = np.count_nonzero(C, axis=1)
    print(f"   weight distribution: ", dict(zip(*np.unique(wts, return_counts=True))))
    qn = q ** n
    for w in range(1, n):
        Vball = ball_volume(q, n, w)
        mu = (q ** dim) * Vball / qn  # E[L]
        # ---- t=2 (exact) ----
        # S_2 = sum_{d!=0} vol_cap2(wt(d))
        cache2 = {}
        S2 = 0
        for wt in wts:
            if wt == 0:
                continue
            if wt not in cache2:
                cache2[wt] = vol_cap2(int(wt), q, n, w)
            S2 += cache2[wt]
        EC2 = (q ** dim) * S2 / qn / 2
        pois2 = mu ** 2 / 2
        ratio2 = EC2 / pois2 if pois2 > 0 else float('nan')
        line = (f"   w={w:2d}  mu={mu:11.4e}  E[C(L,2)]={EC2:11.4e}  "
                f"Poisson={pois2:11.4e}  ratio2={ratio2:.6f}")
        if do_t3 and Ncw <= 6000 and mu > 1e-9:
            # ---- t=3 (exact) : S_3 = sum_{d2!=0,d3!=0,d2!=d3} vol_cap(0,d2,d3) ----
            cache3 = {}
            S3 = 0
            zero_mask = (C == 0)  # (Ncw,n) bool : where each codeword is 0
            for i in range(Ncw):
                d2 = C[i]
                if wts[i] == 0:
                    continue
                a_zero = zero_mask[i]            # (n,) : d2==0 at coord
                # classify every codeword d3 against this d2, per coordinate -> type code 0..4
                b_zero = zero_mask                # (Ncw,n)
                eq = (C == d2[None, :])           # (Ncw,n) : d3==d2
                # type: 0 if a0&b0; 1 if a0&~b0; 2 if ~a0&b0; 3 if ~a0&~b0&eq; 4 else
                a0 = a_zero[None, :]
                t = np.where(a0 & b_zero, 0,
                     np.where(a0 & ~b_zero, 1,
                      np.where(~a0 & b_zero, 2,
                       np.where(eq, 3, 4))))      # (Ncw,n) in 0..4
                # histogram per d3 row: counts of each type across coords
                hist_counts = np.zeros((Ncw, 5), dtype=np.int64)
                for tt in range(5):
                    hist_counts[:, tt] = np.count_nonzero(t == tt, axis=1)
                # exclude d3==0 (wt 0) and d3==d2 (j==i)
                valid = wts > 0
                valid[i] = False
                hv = hist_counts[valid]
                # group identical histograms, evaluate Vol once each
                uniq, cnts = np.unique(hv, axis=0, return_counts=True)
                for row, c in zip(uniq, cnts):
                    key = tuple(int(x) for x in row)
                    if key not in cache3:
                        cache3[key] = vol_cap3_from_hist(key, q, w)
                    S3 += cache3[key] * int(c)
            EC3 = (q ** dim) * S3 / qn / 6
            pois3 = mu ** 3 / 6
            ratio3 = EC3 / pois3 if pois3 > 0 else float('nan')
            line += f"   E[C(L,3)]={EC3:11.4e}  Pois3={pois3:11.4e}  ratio3={ratio3:.6f}"
        print(line)
        sys.stdout.flush()


if __name__ == "__main__":
    # FRI domain mu_8 in F_17 (the fleet's reference 2-power smooth domain), and mu_16 = F_17^*.
    mu8 = field_mu_subgroup(17, 8)
    print("mu_8 in F_17:", mu8)
    # dim-2 super-code (k=1): fast, t=3 enumerable (289 cw). Degenerate (d_min=7) but a sanity anchor.
    run(17, 8, 1, mu8, "mu_8 / F_17, k=1", do_t3=True)
    # dim-3 super-code (k=2, rho=1/4 deep band): the informative case (4913 cw); t=3 ~24M pairs.
    run(17, 8, 2, mu8, "mu_8 / F_17, k=2 (rho=1/4)", do_t3=True)

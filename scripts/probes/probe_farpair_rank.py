#!/usr/bin/env python3
"""#389 route 2 — the far-pair rank law, all strata (probe before formalization).

Claim under test (THE COMPLETE RANK LAW, conjectured exact on EVERY stratum,
including the high-overlap "degeneracy locus" k < o < k+m+1 that
`FarPairRankBound.lean` only handles conditionally via `PairValIndependent`):

  For cores |T| = |T'| = s = k+m+1 with overlap o = |T∩T'|, in the generator
  ensemble c ∈ F^M (M ≥ 2s), the joint event
      {both cores coherent  ∧  coreInterp_T.coeff k = coreInterp_T'.coeff k}
  has EXACT cardinality  q^{M - rank(o)}  with

      rank(o) = 2m + 1 - max(0, o - k).

  Mechanism for o ≥ k+1 (the new part): both interpolants have deg ≤ k and
  agree on o > k nodes, hence are EQUAL — the value match is FORCED and the
  event is exactly "values on T∪T' come from one deg ≤ k polynomial":
  |T∪T'| - (k+1) = 2m+1-(o-k) independent conditions.  No degeneracy strata.

Checks:
  A. exhaustive count at F5 (k=1, m=1, M=6) over all q^M generators, all pairs;
  B. rank of the explicit condition matrix (m + m + 1 functionals on F^M) at
     censused shapes (F97, F12289), random pairs at every overlap stratum;
  C. the refined vs landed capacity-failure-bandwidth denominators at the
     censused shapes (consumer arithmetic only).
"""

from itertools import combinations, product
from math import comb
import random

random.seed(389)


# ---------- GF(p) helpers ----------

def inv(a, p):
    return pow(a, p - 2, p)


def lagrange_coeff_rows(pts, p):
    """Rows L[d][i]: coefficient of X^d in the Lagrange basis poly l_i for
    nodes pts (so coeff_d(interp(vals)) = sum_i L[d][i] * vals[i])."""
    s = len(pts)
    L = [[0] * s for _ in range(s)]
    for i, xi in enumerate(pts):
        # l_i = prod_{j != i} (X - xj) / (xi - xj)
        poly = [1]  # coefficients, low degree first
        denom = 1
        for j, xj in enumerate(pts):
            if j == i:
                continue
            poly = [(-xj * poly[0]) % p] + [
                (poly[d - 1] - xj * poly[d]) % p for d in range(1, len(poly))
            ] + [poly[-1]]
            denom = denom * (xi - xj) % p
        dinv = inv(denom, p)
        for d in range(s):
            L[d][i] = poly[d] * dinv % p if d < len(poly) else 0
    return L


def condition_matrix(p, dom, T, Tp, k, m, M):
    """The 2m+1 functionals on F^M: T-bands, T'-bands, value difference."""
    ptsT = [dom[i] for i in T]
    ptsTp = [dom[i] for i in Tp]
    LT = lagrange_coeff_rows(ptsT, p)
    LTp = lagrange_coeff_rows(ptsTp, p)
    rows = []
    # vals[i] = sum_a c_a * x_i^a  =>  functional row over c
    def row_from(L, pts, d):
        r = [0] * M
        for i, xi in enumerate(pts):
            w = L[d][i]
            xa = 1
            for a in range(M):
                r[a] = (r[a] + w * xa) % p
                xa = xa * xi % p
        return r
    for j in range(m):
        rows.append(row_from(LT, ptsT, k + 1 + j))
    for j in range(m):
        rows.append(row_from(LTp, ptsTp, k + 1 + j))
    rk = row_from(LT, ptsT, k)
    rkp = row_from(LTp, ptsTp, k)
    rows.append([(a - b) % p for a, b in zip(rk, rkp)])
    return rows


def matrank(rows, p):
    rows = [r[:] for r in rows]
    rank, ncols = 0, len(rows[0])
    for col in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        ipiv = inv(rows[rank][col], p)
        rows[rank] = [x * ipiv % p for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(x - f * y) % p for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


# ---------- A. exhaustive at F5 ----------

def exhaustive_check():
    p, k, m = 5, 1, 1
    s = k + m + 1          # 3
    n = 4
    dom = [1, 2, 3, 4]
    M = 2 * s              # 6
    print(f"A. exhaustive: F{p}, n={n}, k={k}, m={m}, s={s}, M={M}")
    cores = list(combinations(range(n), s))
    # precompute lagrange rows per core
    LR = {T: lagrange_coeff_rows([dom[i] for i in T], p) for T in cores}

    def interp_coeffs(T, vals):
        L = LR[T]
        return [sum(L[d][i] * vals[i] for i in range(s)) % p for d in range(s)]

    counts = {}
    for c in product(range(p), repeat=M):
        ev = [sum(c[a] * pow(x, a, p) for a in range(M)) % p for x in dom]
        coh, gam = {}, {}
        for T in cores:
            vals = [ev[i] for i in T]
            cf = interp_coeffs(T, vals)
            ok = all(cf[k + 1 + j] == 0 for j in range(m))
            coh[T] = ok
            gam[T] = cf[k]
        for T in cores:
            for Tp in cores:
                if coh[T] and coh[Tp] and gam[T] == gam[Tp]:
                    counts[(T, Tp)] = counts.get((T, Tp), 0) + 1
    fails = 0
    for T in cores:
        for Tp in cores:
            o = len(set(T) & set(Tp))
            rank = 2 * m + 1 - max(0, o - k)
            want = p ** (M - rank)
            got = counts.get((T, Tp), 0)
            ok = got == want
            fails += not ok
            if not ok:
                print(f"  FAIL T={T} T'={Tp} o={o}: got {got} want {want}")
    print(f"  all {len(cores)**2} pairs: "
          f"{'ALL MATCH rank law 2m+1-max(0,o-k)' if fails == 0 else f'{fails} FAILURES'}")
    return fails == 0


# ---------- B. rank checks at censused shapes ----------

def rank_check(p, n, k, m, trials=40):
    s = k + m + 1
    M = 2 * s
    dom = random.sample(range(1, p), n)
    bad = []
    for o in range(0, s + 1):
        for _ in range(trials):
            T = random.sample(range(n), s)
            if o == s:
                Tp = T[:]
            else:
                inter = random.sample(T, o)
                rest = random.sample([i for i in range(n) if i not in T], s - o)
                Tp = inter + rest
            if len(set(T) & set(Tp)) != o:
                continue
            rows = condition_matrix(p, dom, T, Tp, k, m, M)
            rk = matrank(rows, p)
            want = 2 * m + 1 - max(0, o - k)
            if rk != want:
                bad.append((o, rk, want))
    tag = "ALL MATCH" if not bad else f"{len(bad)} MISMATCHES {bad[:5]}"
    print(f"B. rank law F{p} n={n} k={k} m={m}: {tag}")
    return not bad


# ---------- C. denominator comparison ----------

def denominators(p, n, k, m):
    s = k + m + 1
    Nm = comb(n, s)
    landed = (1 + comb(s, k + 1) * comb(n, m)) * p ** (m + 1) + Nm
    refined = Nm + sum(
        comb(s, j) * comb(n, s - j) * p ** (j - k)
        for j in range(k + 1, s + 1)
    )
    # bandwidth check: bad >= Nm*q / D ; failure-half-field iff D <= 2*Nm
    print(f"C. F{p} n={n} k={k} m={m}: Nm=C({n},{s})={Nm}")
    print(f"   landed  D = {landed}  (bad >= {Nm * p // landed})")
    print(f"   refined D = {refined}  (bad >= {Nm * p // refined})"
          f"   gain x{landed / refined:.3g}")


if __name__ == "__main__":
    okA = exhaustive_check()
    okB = all([
        rank_check(97, 16, 3, 1),
        rank_check(97, 16, 3, 2),
        rank_check(97, 16, 5, 2),
        rank_check(12289, 16, 3, 2),
        rank_check(12289, 16, 3, 4),
    ])
    for (p, n, k, m) in [(97, 16, 3, 1), (97, 16, 3, 2), (12289, 16, 3, 1),
                         (12289, 16, 3, 2), (12289, 64, 3, 2),
                         (12289, 64, 15, 3)]:
        denominators(p, n, k, m)
    print("VERDICT:", "rank law CONFIRMED on all strata" if okA and okB
          else "RANK LAW REFUTED somewhere — do NOT formalize")

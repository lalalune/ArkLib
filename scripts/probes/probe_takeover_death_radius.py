#!/usr/bin/env python3
"""probe_takeover_death_radius.py — the falsifier of CensusUpperExtremalFloor (#357).

The repaired extremality hypothesis (CensusExtremalFloor.lean) asserts: at every grid
agreement a above the crossing, NO stack has more than (#constrainedCensus(a) + 1) bad
scalars. At the measured death radii (census EMPTY: (16,4) at a=7 for p >= 97), this
allows at most ONE bad scalar per stack (the universal floor). A single stack with >= 2
bad scalars there falsifies the hypothesis and kills the census route's upper half.

This probe scans ALL monomial pairs (X^s, X^t) over the smooth domain mu_16 in F_p
(the conjecturally-extremal class: O137/O138 found the per-rung maximizer is always a
monomial pair, and the twisted orbit is affine-equivalent), at agreements a in
{6, 7, 8}, fields p in {97, 193} (mu_16 exists: 16 | p-1).

Method (exact, exhaustive over pairs x witness sets):
  For the stack u = x^s, v = x^t, the line word is w(lam) = u + lam*v — AFFINE in lam.
  For a witness 7-set T, explainability by a deg-<k polynomial is the vanishing of
  (a - k) residual functionals rho_j (a kernel basis of the transposed Vandermonde):
  rho_j . w(lam)|_T = alpha_j + lam*beta_j. So per (pair, T) the bad-lam set is the
  solution set of <= a-k affine equations: empty, a single lam, or all of F_p.
  The pair's bad set is the union over the C(16,a) witness sets T with the no-joint
  clause (not both rows explainable on T). Exact, no sampling.

Verdicts:
  * max #bad over all monomial pairs at the death rung <= 1  -> hypothesis SURVIVES
    its sharpest registered falsifier (for the monomial class);
  * some pair with >= 2 bad lams -> TAKE-OVER FOUND, CensusUpperExtremalFloor FALSE.

Cross-checks: the adjacent pair (s,t) = (a, a-1) must reproduce the constrained census
(empty at a=7, p>=97 per O139/O141); row-codeword pairs (s,t < k) must contribute 0.
"""

import itertools
import sys
import time


def inv_mod(x, p):
    return pow(x, p - 2, p)


def kernel_basis(rows, ncols, p):
    """Basis of the left-kernel functionals of the ncols x len(rows) system:
    given the a x k Vandermonde (rows = points' power rows), return basis of
    {rho in F^a : rho . column = 0 for each of the k columns}."""
    a = len(rows)
    k = ncols
    # Solve rho^T V = 0 where V is a x k. Row-reduce V^T (k x a).
    M = [[rows[i][j] for i in range(a)] for j in range(k)]  # k x a
    # Gaussian elimination on M, track pivot columns
    piv_cols = []
    r = 0
    for c in range(a):
        if r >= k:
            break
        pr = None
        for rr in range(r, k):
            if M[rr][c] % p:
                pr = rr
                break
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = inv_mod(M[r][c], p)
        M[r] = [(x * inv) % p for x in M[r]]
        for rr in range(k):
            if rr != r and M[rr][c] % p:
                f = M[rr][c]
                M[rr] = [(M[rr][j] - f * M[r][j]) % p for j in range(a)]
        piv_cols.append(c)
        r += 1
    free_cols = [c for c in range(a) if c not in piv_cols]
    basis = []
    for fc in free_cols:
        v = [0] * a
        v[fc] = 1
        for ri, pc in enumerate(piv_cols):
            v[pc] = (-M[ri][fc]) % p
        basis.append(v)
    return basis


def run(p, n, k, a_list, max_exp):
    print(f"\n=== F_{p}, mu_{n}, k={k}, agreements {a_list} ===", flush=True)
    # the smooth domain: the n-th roots of unity in F_p
    g = None
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, d, p) != 1
                                        for d in range(1, n) if n % d == 0 and d < n):
            g = cand
            break
    assert g is not None, "no primitive n-th root"
    H = [pow(g, i, p) for i in range(n)]
    assert len(set(H)) == n

    for a in a_list:
        t0 = time.time()
        # witness data: per a-subset T, kernel functionals + row residual flags
        wit = []
        for T in itertools.combinations(range(n), a):
            pts = [H[i] for i in T]
            vrows = [[pow(x, e, p) for e in range(k)] for x in pts]
            basis = kernel_basis(vrows, k, p)
            wit.append((T, pts, basis))
        results = {}
        worst = (0, None)
        for s in range(1, max_exp + 1):
            for t in range(0, s):
                u = [pow(x, s, p) for x in H]
                v = [pow(x, t, p) for x in H]
                bad = set()
                allbad = False
                for (T, pts, basis) in wit:
                    # row explainability (lam-independent): rho.u|T = 0 etc.
                    uT = [u[i] for i in T]
                    vT = [v[i] for i in T]
                    alphas = [sum(r[j] * uT[j] for j in range(a)) % p for r in basis]
                    betas = [sum(r[j] * vT[j] for j in range(a)) % p for r in basis]
                    u_expl = all(x == 0 for x in alphas)
                    v_expl = all(x == 0 for x in betas)
                    if u_expl and v_expl:
                        continue  # joint: T cannot witness badness
                    # solve alpha_j + lam*beta_j = 0 for all j
                    lam_pin = None
                    consistent = True
                    all_lams = True
                    for al, be in zip(alphas, betas):
                        if be == 0:
                            if al != 0:
                                consistent = False
                                break
                            continue
                        all_lams = False
                        lam = (-al * inv_mod(be, p)) % p
                        if lam_pin is None:
                            lam_pin = lam
                        elif lam_pin != lam:
                            consistent = False
                            break
                    if not consistent:
                        continue
                    if all_lams:
                        allbad = True
                        break
                    if lam_pin is not None:
                        bad.add(lam_pin)
                    else:
                        allbad = True
                        break
                count = p if allbad else len(bad)
                results[(s, t)] = count
                if count > worst[0]:
                    worst = (count, (s, t))
        adj = results.get((a, a - 1), "n/a")
        print(f"a={a}: pairs={len(results)}  max #bad={worst[0]} at {worst[1]}  "
              f"adjacent ({a},{a-1}) #bad={adj}  [{time.time()-t0:.1f}s]", flush=True)
        over = {pt: c for pt, c in results.items() if c >= 2}
        if over:
            top = sorted(over.items(), key=lambda kv: -kv[1])[:8]
            print(f"  pairs with >=2 bad: {len(over)}; top: {top}")
        else:
            print("  NO pair with >=2 bad scalars — "
                  "CensusUpperExtremalFloor survives this rung (monomial class)")
    return 0


def main():
    for p in (97, 193):
        run(p, 16, 4, [8, 7, 6], max_exp=15)
    return 0


if __name__ == "__main__":
    sys.exit(main())

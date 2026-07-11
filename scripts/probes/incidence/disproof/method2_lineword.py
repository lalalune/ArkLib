"""
method2_lineword.py — the FAITHFUL in-tree structured bad word: the LINE WORD
    w_i = x_i^{E_HI} + lambda * x_i^{E_LO}
the EXACT object the n32census (O129/O130, census_kernel.c) measured to have list 35 at n=32 and
list 19 at n=16 (the C19 ground truth). lambda = -e_1* = -(max-fiber e_1 value); the in-tree
choice is lambda = -g0^((q-1)/4) with E_HI = k+rho... we generalize and SCAN lambda over the
mu_n orbit of the max-fiber e_1 to find the list-maximizing line word at each (n, rho, band).

The line word X^{E_HI} + lambda X^{E_LO} is a degree-E_HI word (E_HI > k = rho*n), so it is NOT a
codeword; its CODEWORD LIST at agreement a is the count of deg<k polynomials agreeing with it on
>= a points. This is the canonical beyond-capacity structured bad word.

KEY for the DISPROOF: place the list on the WINDOW-INTERIOR (rho*n < a < sqrt(rho)*n) and report
the GROWTH across n=8,16,32. If the interior list grows faster than ~n -> disproof signal.

Bands tested: E_LO = k (the rsCode dim) ; E_HI = E_LO + step, step in {1,2}. (n32: k=16,E_LO=16,
E_HI=18 -> step 2. n16 calibration C19: k=8,E_LO=8,E_HI=10 -> step 2.) We also try step 1.

Exact modular arithmetic only; exact list counter from fastlist.
"""
import sys, itertools, math, json, os
from collections import defaultdict
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import find_mun, eval_poly, interp_poly
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast


def interior_radii(n, rho):
    cap = rho * n
    john = math.sqrt(rho) * n
    return [a for a in range(1, n + 1) if cap < a < john]


def line_word(F, E_HI, E_LO, lam):
    q = F.q
    return [(pow(F.sub[i], E_HI, q) + lam * pow(F.sub[i], E_LO, q)) % q for i in range(F.n)]


def maxfiber_e1_orbit(F, E_HI, E_LO):
    """The in-tree lambda = -e_1* where e_1* is the max-fiber e_1 at the relevant band. The
    canonical value is g0^((q-1)/4); its full mu_n orbit (multiply by mu_n elements) gives the
    tie class. We return the orbit of candidate lambdas = -{ e_1* * mu_n elements } plus the
    canonical -g0^((q-1)/4)-style values, deduped. We also add a few generic lambdas (1, -1,
    random reps) so the scan is honest about whether the in-tree lambda is special."""
    q, n = F.q, F.n
    lams = set()
    # canonical: -g0^((q-1)/4)  (the n32 LAM = -e1*); guard if 4 | q-1
    if (q - 1) % 4 == 0:
        e1star = pow(F.g if False else _primitive_root(q), (q - 1) // 4, q)
        lams.add((-e1star) % q)
        # orbit under mu_n
        for u in F.sub:
            lams.add((-e1star * u) % q)
    lams.add(1 % q)
    lams.add((q - 1) % q)
    lams.add(0)
    return sorted(lams)


def _primitive_root(q):
    # factor q-1
    x = q - 1
    fac = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for h in range(2, q):
        if all(pow(h, (q - 1) // p, q) != 1 for p in fac):
            return h
    raise RuntimeError("no primitive root")


def run(q, n, rho, scan_all_lambda=False, lam_cap=200):
    k = round(rho * n)
    F = Field(q, n, k)
    subs = precompute_subsets(n, k)
    lag = precompute_lagrange(F, subs)
    interior = interior_radii(n, rho)
    budget = n
    out = []
    bands = []
    for step in (1, 2):
        E_LO = k
        E_HI = k + step
        if E_HI <= n:
            bands.append((E_HI, E_LO, step))
    print(f"\n{'='*88}\nLINE WORD  n={n} q={q} rho={rho} k={k}  interior_a={interior}  budget(~n)={budget}\n{'='*88}")
    for (E_HI, E_LO, step) in bands:
        lams = maxfiber_e1_orbit(F, E_HI, E_LO)
        if scan_all_lambda:
            # honest exhaustive-ish: every field lambda is too many; sample a dense set
            lams = sorted(set(lams) | set(range(0, q, max(1, q // lam_cap))))
        best = None
        for lam in lams:
            w = line_word(F, E_HI, E_LO, lam)
            lists = {a: list_count_fast(w, a, F, subs, lag) for a in interior}
            maxL = max(lists.values()) if lists else 0
            if best is None or maxL > best["max_interior_list"]:
                sb = [a for a, L in lists.items() if L > budget]
                best = dict(kind=f"line_X{E_HI}+lamX{E_LO}", n=n, q=q, rho=rho, k=k,
                            E_HI=E_HI, E_LO=E_LO, step=step, lam=lam,
                            interior_a=interior, budget=budget,
                            lists={str(a): L for a, L in lists.items()},
                            max_interior_list=maxL, super_budget=bool(sb),
                            super_budget_radii=sb, n_lambda_scanned=len(lams))
        out.append(best)
        la = " ".join(f"{a}:{best['lists'][str(a)]}" for a in interior)
        print(f"  step={step} E_HI={E_HI} E_LO={E_LO}: BEST over {best['n_lambda_scanned']} lambda "
              f"maxL={best['max_interior_list']:4d} >n={'YES' if best['super_budget'] else '.'}  {la}  (lam={best['lam']})")
    return out


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--rho", type=float, default=0.5)
    ap.add_argument("--scan-all-lambda", action="store_true")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    rows = run(args.q, args.n, args.rho, scan_all_lambda=args.scan_all_lambda)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump(rows, open(args.out, "w"), indent=1)
        print(f"\n[OUT] {args.out}")

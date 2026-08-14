"""
fast_maxlist_compare.py — fast comparison of candidate-word families' interior lists, using the
VERIFIED fastlist exact counter. Answers: does any non-line word (random, monomial, O163 densest
cluster) beat the canonical line word's interior list? (i.e. is the line word near-extremal?)

Families compared at each interior radius a:
  - random words (baseline)
  - monomial words x^e  (e in [k..2n])  (algebraic; PRIOR: NOT extremal)
  - O163 densest-cluster: plurality of L random codewords, L in a sweep
  - line word X^{k+step} + lam X^k at canonical lambda and a lambda sweep
Exact list via fastlist.list_count_fast. n<=16 (C(n,k) tractable for the FULL exact counter).
"""
import sys, math, random, json, os
from collections import Counter
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import eval_poly
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast


def primroot(q):
    x = q - 1; fac = []; d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for h in range(2, q):
        if all(pow(h, (q - 1) // p, q) != 1 for p in fac): return h


def run(q, n, rho, seed=11, n_rand=200, cluster_Ls=(2,3,4,6,8,12,16,24,32,48), cluster_reps=30):
    k = round(rho * n)
    F = Field(q, n, k)
    subs = precompute_subsets(n, k)
    lag = precompute_lagrange(F, subs)
    rng = random.Random(seed)
    cap = rho * n; john = math.sqrt(rho) * n
    interior = [a for a in range(1, n + 1) if cap < a < john]
    best = {a: (0, None) for a in interior}

    def offer(w, label):
        for a in interior:
            L = list_count_fast(w, a, F, subs, lag)
            if L > best[a][0]:
                best[a] = (L, label)

    # random
    for _ in range(n_rand):
        offer([rng.randrange(q) for _ in range(n)], "random")
    # monomial
    for e in range(k, 2 * n + 1):
        offer([pow(x, e, q) for x in F.sub], f"monomial^{e}")
    # O163 densest cluster (plurality of L random codewords)
    for L in cluster_Ls:
        for _ in range(cluster_reps):
            cws = []
            for _ in range(L):
                c = tuple(rng.randrange(q) for _ in range(k))
                cws.append([eval_poly(c, x, q) for x in F.sub])
            w = []
            for i in range(n):
                cnt = Counter(cw[i] for cw in cws)
                mx = max(cnt.values())
                w.append(rng.choice([v for v, ct in cnt.items() if ct == mx]))
            offer(w, f"cluster_L{L}")
    # line words (canonical lambda + sweep)
    g0 = primroot(q)
    lam_canon = (-pow(g0, (q - 1) // 4, q)) % q if (q - 1) % 4 == 0 else 1
    lams = set([0, 1 % q, (q - 1) % q, lam_canon])
    for j in range(64):
        lams.add((j * q // 64) % q)
    for step in (1, 2):
        E_HI = k + step
        if E_HI > n: continue
        for lam in lams:
            w = [(pow(F.sub[i], E_HI, q) + lam * pow(F.sub[i], k, q)) % q for i in range(n)]
            offer(w, f"line_step{step}_lam{'canon' if lam==lam_canon else lam}")

    print(f"\nn={n} q={q} rho={rho} k={k}  interior={interior}  budget(~n)={n}")
    for a in interior:
        L, lab = best[a]
        print(f"  a={a:2d} (f={a/n:.4f}): MAX-LIST={L:4d}  >n={'YES' if L>n else '.'}  by={lab}")
    return dict(q=q, n=n, rho=rho, k=k, interior=interior, budget=n,
                best={str(a): {"max": best[a][0], "by": best[a][1]} for a in interior})


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--rho", type=float, default=0.5)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    r = run(args.q, args.n, args.rho, seed=args.seed)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump(r, open(args.out, "w"), indent=1)
        print(f"[OUT] {args.out}")

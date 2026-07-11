"""
driver.py — unified max-list disproof driver (Method 1) across n=8,16,32.

Search per (n,rho,interior-a): random words, monomials, O163 densest-cluster (plurality of L
random codewords), and incidence-aware HILL-CLIMB (the engine that actually finds the max).
Counting is EXACT (fastlist) when C(n,k) tractable. Parallel over restarts with multiprocessing.

Output: max-list at each interior agreement a, the WORD that achieves it (for reproducibility),
and which strategy found it. The cross-n table answers the growth question.
"""
import sys, itertools, math, random, json, argparse, os
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from fastlist import (Field, precompute_subsets, precompute_lagrange,
                      list_count_fast, hillclimb)
from maxlist_core import eval_poly

def rand_codeword_vals(F, rng):
    c = tuple(rng.randrange(F.q) for _ in range(F.k))
    return [eval_poly(c, x, F.q) for x in F.sub]

def plurality(vals, n, rng):
    w = []
    for i in range(n):
        c = Counter(v[i] for v in vals); m = max(c.values())
        w.append(rng.choice([vv for vv, ct in c.items() if ct == m]))
    return w

def worker(args):
    q, n, rho, seed, n_restarts, hill_iters, cluster_Ls, a_list = args
    rng = random.Random(seed)
    k = round(rho*n)
    F = Field(q, n, k)
    subs = precompute_subsets(n, k)
    lag = precompute_lagrange(F, subs)
    best = {a: (0, None, None) for a in a_list}
    def offer(w, label):
        for a in a_list:
            c = list_count_fast(w, a, F, subs, lag)
            if c > best[a][0]:
                best[a] = (c, list(w), label)
    # random
    for _ in range(n_restarts):
        offer([rng.randrange(q) for _ in range(n)], "random")
    # monomials
    for e in list(range(k, min(n, k+8))) + [n, n+1, 2*n-1, 3*n]:
        offer([pow(x, e, q) for x in F.sub], f"mono^{e}")
    # clusters + hill-climb from each promising cluster
    pool_vals = [rand_codeword_vals(F, rng) for _ in range(96)]
    for L in cluster_Ls:
        reps = max(4, n_restarts // 6)
        local_best_w = None; local_best = -1
        for _ in range(reps):
            vals = [rand_codeword_vals(F, rng) for _ in range(L)]
            w = plurality(vals, n, rng)
            offer(w, f"cluster_L{L}")
            a_mid = a_list[len(a_list)//2]
            c = list_count_fast(w, a_mid, F, subs, lag)
            if c > local_best:
                local_best = c; local_best_w = list(w)
        # hill-climb from this cluster's best word, on each interior a
        if local_best_w is not None:
            for a in a_list:
                bcount, bw = hillclimb(local_best_w, a, F, subs, lag, rng,
                                       iters=hill_iters, pool_vals=pool_vals)
                if bcount > best[a][0]:
                    best[a] = (bcount, list(bw), f"hill_from_cluster_L{L}")
    # also hill-climb from random starts
    for _ in range(max(2, n_restarts//20)):
        w0 = [rng.randrange(q) for _ in range(n)]
        for a in a_list:
            bcount, bw = hillclimb(w0, a, F, subs, lag, rng,
                                   iters=hill_iters, pool_vals=pool_vals)
            if bcount > best[a][0]:
                best[a] = (bcount, list(bw), "hill_from_random")
    return best

def run(q, n, rho, seeds=8, n_restarts=40, hill_iters=40, workers=8, full_threshold=300000):
    k = round(rho*n)
    cap = rho*n; john = math.sqrt(rho)*n
    interior = [a for a in range(1, n) if cap < a < john]
    Cnk = math.comb(n, k)
    if not interior:
        return {"q": q, "n": n, "rho": rho, "k": k, "interior": [], "note": "empty"}
    if Cnk > full_threshold:
        return {"q": q, "n": n, "rho": rho, "k": k, "interior": interior, "Cnk": Cnk,
                "note": f"C(n,k)={Cnk} exceeds exact threshold; use maxlist_n32 lower-bound engine"}
    cluster_Ls = sorted(set([3,4,6,8,12,16,24,32,48,64, n, 2*n]))
    cluster_Ls = [L for L in cluster_Ls if L >= 2]
    tasks = [(q, n, rho, 1000+s, n_restarts, hill_iters, cluster_Ls, interior)
             for s in range(seeds)]
    agg = {a: (0, None, None) for a in interior}
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for fut in as_completed([ex.submit(worker, t) for t in tasks]):
            b = fut.result()
            for a in interior:
                if b[a][0] > agg[a][0]:
                    agg[a] = b[a]
    return {
        "q": q, "n": n, "rho": rho, "k": k, "Cnk": Cnk, "budget_proxy_n": n,
        "cap_agree": cap, "johnson_agree": john, "interior": interior,
        "results": {str(a): {"max": agg[a][0], "by": agg[a][2], "word": agg[a][1]}
                    for a in interior},
    }

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--rho", type=float, required=True)
    ap.add_argument("--seeds", type=int, default=8)
    ap.add_argument("--restarts", type=int, default=40)
    ap.add_argument("--hill", type=int, default=40)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()
    res = run(args.q, args.n, args.rho, seeds=args.seeds, n_restarts=args.restarts,
              hill_iters=args.hill, workers=args.workers)
    print(json.dumps(res, indent=2, default=str))
    if args.out:
        with open(args.out, "w") as f:
            json.dump(res, f, indent=2, default=str)

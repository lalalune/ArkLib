#!/usr/bin/env python3
"""
search_fast.py — fast max-list search for n=8,16 using the validated Python fast counter
(fastlist) with hill-climb, parallelized over seeds with multiprocessing. Avoids C subprocess
overhead (which dominates for tiny counts). For n=8,16 the exact count is sub-ms in Python via
cached Lagrange. Reports max list at each interior agreement a, with the achieving word.
"""
import sys, math, random, json, itertools
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast
from maxlist_core import eval_poly

def _cw(F, rng):
    c = tuple(rng.randrange(F.q) for _ in range(F.k))
    return [eval_poly(c, x, F.q) for x in F.sub]

def _worker(args):
    q, n, k, a, seed, restarts, hill = args
    F = Field(q, n, k)
    subs = precompute_subsets(n, k); lag = precompute_lagrange(F, subs)
    rng = random.Random(seed)
    pool = [_cw(F, rng) for _ in range(96)]
    def sc(w): return list_count_fast(w, a, F, subs, lag)
    best = 0; bestw = None
    def consider(w, lab):
        nonlocal best, bestw
        s = sc(w)
        if s > best: best, bestw = s, list(w)
    # monomials
    for e in list(range(k, min(n, k+8))) + [n-1, n, n+1, 2*n-1, 3*n]:
        consider([pow(x, e, q) for x in F.sub], f"mono^{e}")
    # random
    for _ in range(restarts):
        consider([rng.randrange(q) for _ in range(n)], "rand")
    # cluster + hillclimb from each
    for L in [3,4,6,8,12,16,24,32,48,64]:
        # build a cluster plurality word
        vals = [_cw(F, rng) for _ in range(L)]
        w = []
        for i in range(n):
            cc = Counter(v[i] for v in vals); m = max(cc.values())
            w.append(rng.choice([vv for vv, ct in cc.items() if ct == m]))
        consider(w, f"cluster_L{L}")
        # hillclimb
        w = list(w); cur = sc(w)
        for it in range(hill):
            improved = False
            order = list(range(n)); rng.shuffle(order)
            for i in order:
                bv, bs = w[i], cur
                for p in pool:
                    if p[i] == w[i]: continue
                    old = w[i]; w[i] = p[i]; s = sc(w)
                    if s > bs: bs, bv = s, p[i]
                    w[i] = old
                if bv != w[i]: w[i] = bv; cur = bs; improved = True
            if cur > best: best, bestw = cur, list(w)
            if not improved:
                for _ in range(2):
                    j = rng.randrange(n); w[j] = rng.randrange(q)
                cur = sc(w)
    return best, bestw

def run(q, n, rho, seeds=8, restarts=40, hill=30, workers=8):
    k = round(rho*n)
    cap = rho*n; john = math.sqrt(rho)*n
    interior = [a for a in range(1, n) if cap < a < john]
    out = {}
    for a in interior:
        tasks = [(q, n, k, a, 1000+s, restarts, hill) for s in range(seeds)]
        best = 0; bw = None
        with ProcessPoolExecutor(max_workers=workers) as ex:
            for fut in as_completed([ex.submit(_worker, t) for t in tasks]):
                b, w = fut.result()
                if b > best: best, bw = b, w
        ceil = math.comb(n, k)//math.comb(a, k)
        out[a] = {"max": best, "ceiling": ceil, "budget_n": n, "word": bw}
        print(f"  n={n} rho={rho} a={a}: MAX_LIST={best}  (ceiling={ceil}, budget~n={n})", flush=True)
    return {"q": q, "n": n, "rho": rho, "k": k, "interior": interior, "results": out}

if __name__ == "__main__":
    q = int(sys.argv[1]); n = int(sys.argv[2]); rho = float(sys.argv[3])
    seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 40
    hill = int(sys.argv[6]) if len(sys.argv) > 6 else 30
    res = run(q, n, rho, seeds=seeds, restarts=restarts, hill=hill)
    outp = sys.argv[7] if len(sys.argv) > 7 else None
    if outp:
        with open(outp, "w") as f: json.dump(res, f, indent=2, default=str)

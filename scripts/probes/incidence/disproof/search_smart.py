#!/usr/bin/env python3
"""
search_smart.py — improved max-list search with a CODEWORD-AWARE hill-climb.

Core move (much stronger than random-pool perturbation): maintain a candidate pool of codewords
that currently agree with w on >= a-1 points ("almost-in-list"). For each coordinate i, set w[i]
to the value that the most almost-in-list codewords take at i (plurality), thereby pulling extra
codewords into the >=a list. Iterate. This directly grows list(w,a). Plus random restarts and the
O163 densest-cluster seed. Exact counting via fastlist. Parallel over seeds.
"""
import sys, math, random, json
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast
from maxlist_core import eval_poly, interp_poly, agreement

def _cw(F, rng):
    c = tuple(rng.randrange(F.q) for _ in range(F.k))
    return c, [eval_poly(c, x, F.q) for x in F.sub]

def codewords_near(w, a_minus, F, subs, lag):
    """all distinct deg<k codewords agreeing with w on >= a_minus points (their value vectors)."""
    q = F.q; n = F.n; k = F.k; seen = set(); res = []
    for idx in subs:
        c = interp_poly([F.sub[i] for i in idx], [w[i] for i in idx], q, k)
        if c is None or c in seen: continue
        seen.add(c)
        vals = [eval_poly(c, x, q) for x in F.sub]
        ag = sum(1 for i in range(n) if vals[i] == w[i])
        if ag >= a_minus:
            res.append(vals)
    return res

def _worker(args):
    q, n, k, a, seed, restarts, passes = args
    F = Field(q, n, k)
    subs = precompute_subsets(n, k); lag = precompute_lagrange(F, subs)
    rng = random.Random(seed)
    def sc(w): return list_count_fast(w, a, F, subs, lag)
    best = 0; bestw = None
    def consider(w, lab):
        nonlocal best, bestw
        s = sc(w)
        if s > best: best, bestw = s, list(w)
        return s
    # monomials
    for e in list(range(k, min(n, k+8))) + [n-1, n, n+1, 2*n-1, 3*n]:
        consider([pow(x, e, q) for x in F.sub], f"mono^{e}")
    # random seeds + smart climb
    def smart_climb(w):
        cur = sc(w)
        for _ in range(passes):
            near = codewords_near(w, a-1, F, subs, lag)
            if not near:
                near = codewords_near(w, max(k, a-2), F, subs, lag)
            improved = False
            order = list(range(n)); rng.shuffle(order)
            for i in order:
                cc = Counter(v[i] for v in near)
                if not cc: continue
                # try the top few plurality values at coord i
                for vv, _ in cc.most_common(4):
                    if vv == w[i]: continue
                    old = w[i]; w[i] = vv; s = sc(w)
                    if s > cur:
                        cur = s; improved = True
                        # refresh near occasionally
                    else:
                        w[i] = old
            consider(w, "smart")
            if not improved:
                break
        return cur
    # cluster seeds
    for L in [3,4,6,8,12,16,24,32,48,64]:
        cw = [_cw(F, rng) for _ in range(L)]
        vals = [v for _, v in cw]
        w = []
        for i in range(n):
            cc = Counter(v[i] for v in vals); m = max(cc.values())
            w.append(rng.choice([vv for vv, ct in cc.items() if ct == m]))
        consider(w, f"cluster_L{L}")
        smart_climb(list(w))
    for _ in range(restarts):
        w = [rng.randrange(q) for _ in range(n)]
        smart_climb(w)
    return best, bestw

def run(q, n, rho, seeds=8, restarts=12, passes=12, workers=8):
    k = round(rho*n)
    cap = rho*n; john = math.sqrt(rho)*n
    interior = [a for a in range(1, n) if cap < a < john]
    out = {}
    for a in interior:
        tasks = [(q, n, k, a, 2000+s, restarts, passes) for s in range(seeds)]
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
    restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 12
    passes = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    outp = sys.argv[7] if len(sys.argv) > 7 else None
    res = run(q, n, rho, seeds=seeds, restarts=restarts, passes=passes)
    if outp:
        with open(outp, "w") as f: json.dump(res, f, indent=2, default=str)

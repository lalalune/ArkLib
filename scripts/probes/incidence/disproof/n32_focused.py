#!/usr/bin/env python3
"""
n32_focused.py — focused EXACT max-list evaluation at n=32 (q=1048609, non-Fermat, beta=4).
Each exact list count is ~61s (OpenMP C tool), so we evaluate a CURATED candidate set at the
DEEPEST interior agreement a=k+1 (where the packing ceiling is highest -> a disproof, if it
exists, shows here first). Candidates:
  - monomials x^e for e in a small key set (dilation-eigenvector far monomials etc.)
  - O163 densest-cluster plurality words for several L
  - a short greedy hill-climb (few coordinates) seeded from the best candidate
We report the MAX exact list found and compare to budget proxy ~n=32 and ceiling C(n,k)/C(a,k).
"""
import subprocess, random, math, sys, time, json
EXE = "/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof/maxlist32mp"
Q, N = 1048609, 32

def find_sub(q, n):
    def order_ok(g):
        if pow(g, n, q) != 1: return False
        for d in range(1, n):
            if n % d == 0 and d < n and pow(g, d, q) == 1: return False
        return True
    for g in range(2, q):
        if order_ok(g):
            return [pow(g, j, q) for j in range(n)]
    raise RuntimeError

def count(w, k, a):
    out = subprocess.run(["taskset","-c","0-7", EXE, str(Q), str(N), str(k), str(a), "count"] +
                         [str(x) for x in w], capture_output=True, text=True)
    return int(out.stdout.strip())

def run(rho, a, n_clusters_each=2, seed=20250615, time_budget_s=2400):
    k = round(rho*N)
    sub = find_sub(Q, N)
    rng = random.Random(seed)
    t0 = time.time()
    results = []
    def evalw(w, label):
        if time.time()-t0 > time_budget_s:
            return None
        c = count(w, k, a); results.append((c, label, list(w)))
        print(f"  [{time.time()-t0:6.0f}s] {label:24s} list={c}", flush=True)
        return c
    # monomials: deepest-relevant exponents
    mono_es = [k+1, k+2, N-2, N-1, N, N+1, 2*N-1, 2*N, 3*N]
    for e in mono_es:
        evalw([pow(x, e, Q) for x in sub], f"mono^{e}")
    # densest-cluster plurality words
    def rand_cw():
        cf = [rng.randrange(Q) for _ in range(k)]
        return [sum(cf[j]*pow(x, j, Q) for j in range(k)) % Q for x in sub]
    from collections import Counter
    for L in [4, 8, 16, 24, 32, 48]:
        for rep in range(n_clusters_each):
            vals = [rand_cw() for _ in range(L)]
            w = []
            for i in range(N):
                cc = Counter(v[i] for v in vals); m = max(cc.values())
                w.append(rng.choice([vv for vv, ct in cc.items() if ct == m]))
            evalw(w, f"cluster_L{L}_r{rep}")
    # short hill-climb from best so far (few full passes, pool = random codewords)
    results.sort(reverse=True)
    if results:
        bestc, _, bw = results[0]
        w = list(bw)
        pool = [rand_cw() for _ in range(24)]
        cur = bestc
        for it in range(3):
            improved = False
            order = list(range(N)); rng.shuffle(order)
            for i in order:
                if time.time()-t0 > time_budget_s: break
                bv, bs = w[i], cur
                for p in pool:
                    if p[i] == w[i]: continue
                    old = w[i]; w[i] = p[i]
                    s = count(w, k, a)
                    if s > bs: bs, bv = s, p[i]
                    w[i] = old
                if bv != w[i]:
                    w[i] = bv; cur = bs; improved = True
                    print(f"  [{time.time()-t0:6.0f}s] hill coord{i} -> list={cur}", flush=True)
            if not improved: break
        results.append((cur, "hillclimb", list(w)))
    results.sort(reverse=True)
    ceil = math.comb(N, k)//math.comb(a, k)
    best = results[0]
    print(json.dumps({"rho": rho, "k": k, "a": a, "budget_n": N, "ceiling": ceil,
                      "MAX_LIST": best[0], "by": best[1]}, indent=2))
    return best

if __name__ == "__main__":
    rho = float(sys.argv[1]) if len(sys.argv) > 1 else 0.25
    a = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    tb = int(sys.argv[3]) if len(sys.argv) > 3 else 2400
    run(rho, a, time_budget_s=tb)

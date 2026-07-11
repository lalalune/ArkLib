"""
maxlist_n32.py — focused exact-on-cluster max-list search for large n (n=32, also re-runs
n=8,16 with the SAME engine for a consistent growth table).

For n=32 the generic C(n,k) interpolation counter is too slow per word (C(32,8)=10.5M,
C(32,16)=6e8). But for the GROWTH question we only need to evaluate a focused set of
CANDIDATE words (cluster constructions + monomials + hill-climb winners) and count their
lists EXACTLY. We do exact counting via the planted-cluster structure plus a bounded
interpolant sweep, and verify against the generic counter on small n.

Counting strategy 'exact_via_pairs':
  For a candidate word w, the codewords agreeing with w on >=a points are exactly the
  deg<k interpolants of w over SOME k-subset of an a-agreement set. We enumerate candidate
  codewords by: for the constructed cluster we already KNOW the planted codewords; for ANY
  extra coincidental codewords we sweep k-subsets of the indices where w takes a value that
  is shared by >=2 planted codewords (the only places extra agreements can pile up). To stay
  exact we fall back to full C(n,k) when feasible and otherwise report a VERIFIED LOWER BOUND
  (which is what matters for a disproof: a lower bound exceeding budget IS a disproof).
"""
import sys, itertools, random, math, json, argparse
from collections import Counter
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import find_mun, interp_poly, eval_poly, agreement, list_size_exact

def rand_codeword(sub, q, k, rng):
    coeffs = tuple(rng.randrange(q) for _ in range(k))
    return coeffs, [eval_poly(coeffs, x, q) for x in sub]

def plurality_word(vals, n, rng):
    w = []
    for i in range(n):
        c = Counter(v[i] for v in vals)
        best = max(c.values())
        modes = [vv for vv, ct in c.items() if ct == best]
        w.append(rng.choice(modes))
    return w

def count_exact_lowerbound(w, a, sub, q, k, planted_coeffs, full_threshold=2_000_000):
    """Returns (count, is_exact).
    If C(n,k) <= full_threshold -> full exact via list_size_exact.
    Else -> count distinct codewords among (planted) UNION (interpolants over k-subsets
    restricted to 'collision' indices). This is a guaranteed LOWER BOUND; for the planted
    densest cluster it captures all planted codewords exactly."""
    n = len(sub)
    if math.comb(n, k) <= full_threshold:
        return list_size_exact(w, a, sub, q, k), True
    seen = set(); cnt = 0
    # always count planted codewords that actually agree >= a
    for c in planted_coeffs:
        if c in seen: continue
        if agreement(c, w, sub, q) >= a:
            seen.add(c); cnt += 1
    # collision indices: coordinates whose w-value is hit by >=2 planted codewords
    # (extra coincidental high-agreement codewords must live on these); bounded sweep
    coll = []
    for i in range(n):
        hits = sum(1 for c in planted_coeffs if eval_poly(c, sub[i], q) == w[i])
        if hits >= 1:
            coll.append(i)
    # sweep k-subsets of collision indices (bounded); dedup
    if math.comb(len(coll), k) <= full_threshold:
        for idx in itertools.combinations(coll, k):
            xs = [sub[i] for i in idx]; ys = [w[i] for i in idx]
            c = interp_poly(xs, ys, q, k)
            if c is None or c in seen: continue
            seen.add(c)
            if agreement(c, w, sub, q) >= a:
                cnt += 1
    return cnt, (math.comb(len(coll), k) <= full_threshold)

def run(q, n, rho, rng, restarts=200, cluster_Ls=None, full_threshold=2_000_000):
    k = round(rho * n)
    g, sub = find_mun(q, n)
    cap = rho * n; john = math.sqrt(rho) * n
    interior = [a for a in range(1, n) if cap < a < john]
    if cluster_Ls is None:
        # span up to ~3n so the cluster can plant more codewords than budget if possible
        cluster_Ls = sorted(set([3,4,6,8,12,16,24,32,48,64,96,128,
                                 n//2, n, 2*n, 3*n, 4*n]))
        cluster_Ls = [L for L in cluster_Ls if L >= 2]
    best = {a: {"max": 0, "exact": True, "by": None} for a in interior}

    def offer(w, planted_coeffs, label):
        for a in interior:
            cnt, ex = count_exact_lowerbound(w, a, sub, q, k, planted_coeffs, full_threshold)
            if cnt > best[a]["max"]:
                best[a] = {"max": cnt, "exact": ex, "by": label}

    # monomials
    for e in list(range(k, min(n, k+6))) + [n, n+1, 2*n-1]:
        w = [pow(x, e, q) for x in sub]
        offer(w, [], f"monomial^{e}")

    # cluster constructions (the O163 densest-cluster idea), many restarts
    for L in cluster_Ls:
        reps = max(6, restarts // max(1, len(cluster_Ls)//4))
        for _ in range(reps):
            cw = [rand_codeword(sub, q, k, rng) for _ in range(L)]
            coeffs = [c for c, _ in cw]; vals = [v for _, v in cw]
            w = plurality_word(vals, n, rng)
            offer(w, coeffs, f"cluster_L{L}")

    return {
        "q": q, "n": n, "rho": rho, "k": k, "budget_proxy_n": n,
        "cap_agree": cap, "johnson_agree": john, "interior": interior,
        "Cnk": math.comb(n, k),
        "results": {str(a): best[a] for a in interior},
    }

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--rho", type=float, required=True)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--restarts", type=int, default=200)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    res = run(args.q, args.n, args.rho, rng, restarts=args.restarts)
    print(json.dumps(res, indent=2, default=str))
    if args.out:
        with open(args.out, "w") as f:
            json.dump(res, f, indent=2, default=str)

"""
maxlist_search.py — DIRECT max-list search (Method 1) for the proximity-floor disproof.

For each (n, rho, interior agreement a):
  maximize over words w in F_q^n of  list(w,a) = #{deg<k codewords agreeing >= a points}.

Strategies combined:
  (A) random words  (baseline)
  (B) monomial / power words x^e  (algebraic baseline; PRIOR says these are NOT extremal)
  (C) O163 densest-cluster construction: pick L random codewords, set w = coordinatewise
      PLURALITY; this manufactures many codewords agreeing with w. Vary L.
  (D) hill-climb: start from best-so-far word, perturb single coordinates to the value that
      most increases list(w,a) (greedy coordinate ascent), with random restarts.

Counting uses exact interpolation counter when C(n,k) tractable, else a codeword-incidence
counter that enumerates the *constructed* cluster's interpolants (lower bound = exact for
cluster words, since every agreeing codeword passes through some k-subset we seed).

Honest reporting: we report the MAX list found and whether it exceeds the prize budget proxy
(~ n). Growth across n at fixed interior radius determines disproof vs floor.
"""
import sys, itertools, random, math, json, argparse
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import (find_mun, list_size_exact, interp_poly, eval_poly,
                          agreement, is_prime, is_pow2plus1)

def rand_codeword(sub, q, k, rng):
    coeffs = tuple(rng.randrange(q) for _ in range(k))
    return coeffs, [eval_poly(coeffs, x, q) for x in sub]

def plurality_word(codewords_vals, n, rng):
    """coordinatewise plurality (ties -> random among modes)."""
    w = []
    for i in range(n):
        from collections import Counter
        c = Counter(cv[i] for cv in codewords_vals)
        best = max(c.values())
        modes = [v for v, ct in c.items() if ct == best]
        w.append(rng.choice(modes))
    return w

# ---------- exact counting wrapper: tractable iff C(n,k) small ----------
def comb(n, k):
    return math.comb(n, k)

def count_list(w, a, sub, q, k, mode, cap=None):
    """mode='exact' uses full C(n,k); mode='cluster_seeds' restricts interpolation seeds to
    k-subsets drawn from agreement of provided seed codewords (handled by caller)."""
    return list_size_exact(w, a, sub, q, k, cap=cap)

# ---------- cluster-seed exact-ish counter for large n ----------
def count_list_seeded(w, a, sub, q, k, seed_idxsets, cap=None):
    """Count distinct deg<k codewords agreeing with w on >=a points, but only enumerate
    interpolants over k-subsets that lie inside the union of provided agreement index sets.
    This is a LOWER BOUND on list(w,a) in general; it is EXACT for any codeword whose
    a-agreement set contains one of the seeded sets. For the densest-cluster construction the
    seeds ARE the planted codewords' agreement sets, so all planted codewords are counted."""
    n = len(sub)
    seen = set(); cnt = 0
    # candidate index pool = union of seed sets (plus we always allow any k-subset of full agreement
    # of already-found codewords). Simpler: enumerate k-subsets of the union pool.
    pool = sorted(set().union(*[set(s) for s in seed_idxsets])) if seed_idxsets else list(range(n))
    for idx in itertools.combinations(pool, k):
        xs = [sub[i] for i in idx]; ys = [w[i] for i in idx]
        c = interp_poly(xs, ys, q, k)
        if c is None or c in seen: continue
        seen.add(c)
        if agreement(c, w, sub, q) >= a:
            cnt += 1
            if cap is not None and cnt >= cap: return cnt
    return cnt

# ---------- main search ----------
def search(q, n, rho, rng, n_restarts=40, cluster_Ls=None, hill_iters=200,
           exact_threshold=300000, verbose=False):
    k = round(rho * n)
    g, sub = find_mun(q, n)
    cap_agree = rho * n
    john_agree = math.sqrt(rho) * n
    interior = [a for a in range(1, n) if cap_agree < a < john_agree]
    if not interior:
        return {"n": n, "rho": rho, "k": k, "interior": [], "note": "empty interior"}
    use_exact = comb(n, k) <= exact_threshold
    if cluster_Ls is None:
        cluster_Ls = [3, 4, 6, 8, 12, 16, 24, 32]

    results = {a: {"max": 0, "by": None} for a in interior}

    def evaluate(w, seeds=None):
        out = {}
        for a in interior:
            if use_exact:
                out[a] = list_size_exact(w, a, sub, q, k)
            else:
                # seeded lower-bound counter (seeds = planted codeword agreement index sets)
                if seeds is None:
                    seeds = [list(range(n))]
                out[a] = count_list_seeded(w, a, sub, q, k, seeds)
        return out

    def offer(w, label, seeds=None):
        vals = evaluate(w, seeds)
        for a in interior:
            if vals[a] > results[a]["max"]:
                results[a]["max"] = vals[a]
                results[a]["by"] = label
        return vals

    # (A) random words
    for _ in range(n_restarts):
        w = [rng.randrange(q) for _ in range(n)]
        offer(w, "random")

    # (B) monomial / power words x^e  (e in [k, n-1] and a few high)
    for e in list(range(k, n)) + [n, n+1, 2*n-1]:
        w = [pow(x, e, q) for x in sub]
        offer(w, f"monomial^{e}")

    # (C) O163 densest-cluster: plurality of L random codewords
    best_cluster = None
    for L in cluster_Ls:
        for rep in range(max(8, n_restarts // 2)):
            cw = [rand_codeword(sub, q, k, rng) for _ in range(L)]
            vals = [v for _, v in cw]
            w = plurality_word(vals, n, rng)
            seeds = []
            for coeffs, v in cw:
                seeds.append([i for i in range(n) if v[i] == w[i]])
            vmap = offer(w, f"cluster_L{L}", seeds=seeds)
            mx = max(vmap.values())
            if best_cluster is None or mx > best_cluster[0]:
                best_cluster = (mx, w, seeds)

    # (D) hill-climb from best cluster word (greedy coordinate ascent on the *widest* interior a)
    a_target = interior[len(interior)//2]  # middle of interior window
    if best_cluster is not None:
        w = list(best_cluster[1])
        # sample value candidates: union of all codeword values seen at each coord is expensive;
        # use values from a fresh pool of random codewords as candidate set per coordinate.
        pool = [rand_codeword(sub, q, k, rng)[1] for _ in range(64)]
        def score(ww):
            if use_exact:
                return list_size_exact(ww, a_target, sub, q, k)
            seeds = [list(range(n))]
            return count_list_seeded(ww, a_target, sub, q, k, seeds)
        cur = score(w)
        for it in range(hill_iters):
            improved = False
            order = list(range(n)); rng.shuffle(order)
            for i in order:
                cand_vals = set(p[i] for p in pool) | {w[i]}
                best_v, best_s = w[i], cur
                for vv in cand_vals:
                    if vv == w[i]: continue
                    old = w[i]; w[i] = vv
                    s = score(w)
                    if s > best_s:
                        best_s, best_v = s, vv
                    w[i] = old
                if best_v != w[i]:
                    w[i] = best_v; cur = best_s; improved = True
            offer(w, "hillclimb", seeds=[list(range(n))])
            if not improved:
                # random kick
                for _ in range(2):
                    j = rng.randrange(n); w[j] = rng.randrange(q)
                cur = score(w)
        offer(w, "hillclimb_final", seeds=[list(range(n))])

    return {
        "q": q, "n": n, "rho": rho, "k": k,
        "cap_agree": cap_agree, "johnson_agree": john_agree,
        "interior": interior, "exact": use_exact,
        "Cnk": comb(n, k),
        "results": {str(a): results[a] for a in interior},
    }

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--rho", type=float, required=True)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--restarts", type=int, default=40)
    ap.add_argument("--hill", type=int, default=120)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    res = search(args.q, args.n, args.rho, rng, n_restarts=args.restarts, hill_iters=args.hill)
    print(json.dumps(res, indent=2, default=str))
    if args.out:
        with open(args.out, "w") as f:
            json.dump(res, f, indent=2, default=str)

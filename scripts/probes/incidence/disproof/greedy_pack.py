"""
greedy_pack.py — REALIZABILITY of the combinatorial ceiling L <= C(n,k)/C(a,k).

The ceiling comes from k-subset disjointness: each codeword in the list "owns" C(a,k) k-subsets
of [n], and distinct codewords own disjoint k-subset families (a k-subset interpolates a unique
poly). Question: can RS codewords over mu_n realize a list anywhere near this ceiling at a FIXED
interior agreement a, and how does the realized max grow with n?

Construction tried here (strongest realizable):
  GREEDY PACKING. Maintain a word w (initially a random codeword). Repeatedly search for a NEW
  codeword c that agrees with the CURRENT w on >=a points; if found, "lock in" its agreement by
  keeping w fixed there. Equivalent reformulation that we use: pick an agreement set S (|S|=a) and
  a value assignment on S that is the restriction of MANY codewords -> but a deg<k poly is fixed by
  k points, so once we fix w on >=k coordinates, at most ONE codeword agrees there. The ONLY way to
  get list>1 is codewords agreeing with w on DIFFERENT a-subsets that overlap in <=k-1 coords.

  So the realizable construction is: choose a family F of deg<k polys with pairwise agreement <=k-1,
  then set w = plurality; list(w,a) counts those f in F with agree(f,w)>=a PLUS any coincidental
  extra codewords. We GREEDILY grow F to maximize the number simultaneously agreeing with the
  plurality on >=a points. We seed F with structured bundles (monomial translates, coset families)
  and random codewords, then local-improve.

This directly tests: does realized max-list >> n (DISPROOF) or stay ~ n (FLOOR)?
"""
import sys, itertools, math, random, json, argparse
from collections import Counter
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import find_mun, eval_poly, agreement, interp_poly

def codeword_vals(coeffs, sub, q):
    return [eval_poly(coeffs, x, q) for x in sub]

def plurality(vals, n, rng):
    w = []
    for i in range(n):
        c = Counter(v[i] for v in vals); m = max(c.values())
        w.append(rng.choice([vv for vv, ct in c.items() if ct == m]))
    return w

def count_agreeing(F_vals, w, a):
    n = len(w)
    return sum(1 for v in F_vals if sum(1 for i in range(n) if v[i] == w[i]) >= a)

def exact_extra_list(w, a, sub, q, k, max_Cnk=3_000_000):
    """If C(n,k) tractable, return the EXACT full list(w,a). Else None."""
    n = len(sub)
    if math.comb(n, k) > max_Cnk:
        return None
    seen = set(); cnt = 0
    for idx in itertools.combinations(range(n), k):
        c = interp_poly([sub[i] for i in idx], [w[i] for i in idx], q, k)
        if c is None or c in seen: continue
        seen.add(c)
        if agreement(c, w, sub, q) >= a: cnt += 1
    return cnt

def greedy_pack(q, n, rho, a, rng, rounds=4000, family_target=None):
    k = round(rho*n)
    g, sub = find_mun(q, n)
    if family_target is None:
        family_target = max(64, 4*n)
    # candidate-codeword generator: random + monomial bundles + coset bundles
    def rand_coeffs(): return tuple(rng.randrange(q) for _ in range(k))
    # Greedy: maintain F (list of codeword value-vectors) and w=plurality(F). At each round,
    # propose a candidate codeword; accept if it raises count_agreeing(F+{c}, plurality, a).
    F = [codeword_vals(rand_coeffs(), sub, q)]
    w = list(F[0])
    best = 1
    stale = 0
    for r in range(rounds):
        cand = codeword_vals(rand_coeffs(), sub, q)
        trial = F + [cand]
        w2 = plurality(trial, n, rng)
        cnt = count_agreeing(trial, w2, a)
        if cnt > best or (cnt >= best and len(trial) <= family_target):
            if cnt >= best:
                F = trial; w = w2;
                if cnt > best:
                    best = cnt; stale = 0
                else:
                    stale += 1
            if len(F) > family_target:
                # drop the codeword contributing least
                contrib = []
                for j in range(len(F)):
                    sub_w = plurality(F[:j]+F[j+1:], n, rng)
                    contrib.append(count_agreeing(F[:j]+F[j+1:], sub_w, a))
                jdrop = max(range(len(F)), key=lambda j: contrib[j])
                F = F[:jdrop]+F[jdrop+1:]
        else:
            stale += 1
        if stale > 600:
            break
    # final exact count if possible
    exact = exact_extra_list(w, a, sub, q, k)
    return {"a": a, "k": k, "family_size": len(F), "agreeing_planted": best,
            "exact_full_list": exact, "word": w}

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--rho", type=float, required=True)
    ap.add_argument("--a", type=int, required=True)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--rounds", type=int, default=4000)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    res = greedy_pack(args.q, args.n, args.rho, args.a, rng, rounds=args.rounds)
    res2 = {kk: vv for kk, vv in res.items() if kk != "word"}
    print(json.dumps(res2, indent=2, default=str))

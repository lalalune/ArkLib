"""
growth_table.py — the GROWTH table for the line-word (Method-2) structured bad word, at a FIXED
interior AGREEMENT FRACTION across n. This is the decisive disproof/floor diagnostic.

For the floor conjecture (lists <= budget ~ n at interior radii), we ask: does max-list at a fixed
interior fraction f = a/n grow faster than ~n across n=8,16,32?

We compute the EXACT list of the best line word X^{k+step} + lam X^k at agreement a = round(f*n),
for f in the common interior fractions, scanning lam over the max-fiber orbit + a dense sample.
n=8,16 here (exact, Python). n=32 handled by the C kernel (lineword_n32.c) separately.
"""
import sys, math, json, os
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import eval_poly
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast


def line_word(F, E_HI, E_LO, lam):
    q = F.q
    return [(pow(F.sub[i], E_HI, q) + lam * pow(F.sub[i], E_LO, q)) % q for i in range(F.n)]


def primitive_root(q):
    x = q - 1; fac = []; d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for h in range(2, q):
        if all(pow(h, (q - 1) // p, q) != 1 for p in fac):
            return h
    raise RuntimeError


def lambda_candidates(F, dense=64):
    q = F.q
    lams = set([0, 1 % q, (q - 1) % q])
    if (q - 1) % 4 == 0:
        e1 = pow(primitive_root(q), (q - 1) // 4, q)
        lams.add((-e1) % q)
        for u in F.sub:                       # mu_n orbit of the max-fiber e1
            lams.add((-e1 * u) % q)
    for j in range(dense):                    # honest dense sample of generic lambdas
        lams.add((j * q // dense) % q)
    return sorted(lams)


def interior_fractions(n, rho):
    cap = rho * n; john = math.sqrt(rho) * n
    return [(a, a / n) for a in range(1, n + 1) if cap < a < john]


def best_lineword_list(F, subs, lag, a, steps=(1, 2), dense=64):
    """max over (step, lambda) of list(line_word, a). Returns (best_list, best_meta)."""
    k = F.k
    bestL, meta = 0, None
    for step in steps:
        E_HI, E_LO = k + step, k
        if E_HI > F.n:
            continue
        for lam in lambda_candidates(F, dense=dense):
            w = line_word(F, E_HI, E_LO, lam)
            L = list_count_fast(w, a, F, subs, lag)
            if L > bestL:
                bestL, meta = L, dict(step=step, E_HI=E_HI, E_LO=E_LO, lam=lam)
    return bestL, meta


def run(configs, rho, dense=64):
    table = {}
    for (n, q) in configs:
        k = round(rho * n)
        F = Field(q, n, k)
        subs = precompute_subsets(n, k)
        lag = precompute_lagrange(F, subs)
        fr = interior_fractions(n, rho)
        row = {}
        for (a, f) in fr:
            L, meta = best_lineword_list(F, subs, lag, a, dense=dense)
            row[a] = dict(frac=round(f, 4), best_list=L, budget=n, super_budget=(L > n), meta=meta)
        table[n] = dict(q=q, k=k, rho=rho, radii=row)
        print(f"\nn={n} q={q} rho={rho} k={k}:")
        for a, d in row.items():
            print(f"   a={a:2d} (f={d['frac']:.4f}): best_line_list={d['best_list']:4d}  "
                  f">n={'YES' if d['super_budget'] else '.'}  (budget={d['budget']}, "
                  f"step={d['meta']['step'] if d['meta'] else '-'}, lam={d['meta']['lam'] if d['meta'] else '-'})")
    return table


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--rho", type=float, default=0.5)
    ap.add_argument("--dense", type=int, default=64)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    configs = [(8, 4129), (16, 65617)]
    table = run(configs, args.rho, dense=args.dense)
    # growth summary at common fractions
    print("\n=== GROWTH at common interior fractions (best line-word list) ===")
    fracs = {}
    for n, d in table.items():
        for a, dd in d["radii"].items():
            fracs.setdefault(dd["frac"], {})[n] = dd["best_list"]
    print(f"{'frac':8s} " + " ".join(f"n={n}" for n, _ in table.items()) + "   ratio-to-n")
    for f in sorted(fracs):
        cols = fracs[f]
        s = f"{f:<8.4f} " + " ".join(f"{cols.get(n,'-'):>4}" for n, _ in table.items())
        ratios = " ".join(f"{cols[n]/n:.2f}" for n, _ in table.items() if n in cols)
        print(s + f"   [{ratios}]")
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump(table, open(args.out, "w"), indent=1)
        print(f"\n[OUT] {args.out}")

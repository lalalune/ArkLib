"""
fastlist.py — fast EXACT list counter + incidence-aware hill-climb for the disproof search.

Speedups vs maxlist_core:
  - precompute power table P[i][j] = x_i^j  (j<k)  for the eval domain.
  - interpolation via precomputed Lagrange basis weights is overkill; instead we count the
    list by the LINE/CURVE-INCIDENCE view that is exact for a>=k:
        list(w,a) = # distinct deg<k polynomials p with |{i: p(x_i)=w_i}| >= a.
    Each such p is determined by its values on any k agreement points => enumerate k-subsets,
    interpolate, dedup, check agreement. We cache Lagrange basis L_{idx} so interpolation is
    a dot product, and we evaluate the resulting poly on all n points with the power table.
  - For the hill-climb we only need the COUNT, and we cap enumeration when C(n,k) is small.

Exactness verified against maxlist_core.list_size_exact in self-test.
"""
import sys, itertools, math, random
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import find_mun, eval_poly, interp_poly, agreement, list_size_exact

class Field:
    def __init__(self, q, n, k):
        self.q = q; self.n = n; self.k = k
        self.g, self.sub = find_mun(q, n)
        self.inv = {}  # lazy
    def inverse(self, x):
        x %= self.q
        v = self.inv.get(x)
        if v is None:
            v = pow(x, self.q-2, self.q); self.inv[x] = v
        return v

def precompute_subsets(n, k):
    return list(itertools.combinations(range(n), k))

def precompute_lagrange(F, subsets):
    """For each k-subset idx, precompute, for each target point t in 0..n-1, the row of
    Lagrange weights so that p(x_t) = sum_m weight[t][m]*y_{idx[m]} where y are the values
    at the subset points. Returns dict idx-> (weights as list over t of list over m)."""
    q = F.q; sub = F.sub; n = F.n; k = F.k
    cache = {}
    for idx in subsets:
        xs = [sub[i] for i in idx]
        # Lagrange basis value at target x_t: L_m(x_t) = prod_{j!=m} (x_t - xs[j])/(xs[m]-xs[j])
        # precompute denominators
        denom = []
        for m in range(k):
            d = 1
            for j in range(k):
                if j != m:
                    d = (d * (xs[m]-xs[j])) % q
            denom.append(F.inverse(d))
        W = []
        for t in range(n):
            xt = sub[t]
            row = []
            for m in range(k):
                num = 1
                for j in range(k):
                    if j != m:
                        num = (num * (xt - xs[j])) % q
                row.append((num * denom[m]) % q)
            W.append(row)
        cache[idx] = W
    return cache

def list_count_fast(w, a, F, subsets, lag):
    """Exact list(w,a) for a>=k via cached Lagrange evaluation. Dedup by full eval signature."""
    q = F.q; n = F.n; k = F.k
    seen = set(); cnt = 0
    for idx in subsets:
        W = lag[idx]
        ys = [w[idx[m]] for m in range(k)]
        # signature = tuple of p(x_t) for all t  (dedups identical polynomials)
        sig = []
        ag = 0
        for t in range(n):
            row = W[t]
            v = 0
            for m in range(k):
                v += row[m]*ys[m]
            v %= q
            sig.append(v)
            if v == w[t]:
                ag += 1
        sig = tuple(sig)
        if sig in seen:
            continue
        seen.add(sig)
        if ag >= a:
            cnt += 1
    return cnt

# ---------- incidence-aware hill-climb ----------
def hillclimb(w0, a, F, subsets, lag, rng, iters=60, pool_vals=None, restart_kicks=2):
    """Greedy coordinate ascent maximizing list(w,a). Candidate values per coordinate:
    pool_vals (a set of 'codeword values seen') plus current; if pool_vals None, derive from
    random codewords."""
    n = F.n; q = F.q; k = F.k
    w = list(w0)
    def score(ww): return list_count_fast(ww, a, F, subsets, lag)
    cur = score(w); best = cur; bestw = list(w)
    if pool_vals is None:
        pool_vals = []
        for _ in range(64):
            c = tuple(rng.randrange(q) for _ in range(k))
            pool_vals.append([eval_poly(c, x, q) for x in F.sub])
    for it in range(iters):
        improved = False
        order = list(range(n)); rng.shuffle(order)
        for i in order:
            cands = set(p[i] for p in pool_vals) | {w[i]}
            bv, bs = w[i], cur
            for vv in cands:
                if vv == w[i]: continue
                old = w[i]; w[i] = vv
                s = score(w)
                if s > bs: bs, bv = s, vv
                w[i] = old
            if bv != w[i]:
                w[i] = bv; cur = bs; improved = True
        if cur > best:
            best = cur; bestw = list(w)
        if not improved:
            for _ in range(restart_kicks):
                j = rng.randrange(n); w[j] = rng.randrange(q)
            cur = score(w)
    return best, bestw

# ---------- self test ----------
if __name__ == "__main__":
    rng = random.Random(3)
    for q,n,rho in [(4129,8,0.25),(4129,8,0.5),(65617,16,0.25)]:
        k = round(rho*n)
        F = Field(q,n,k)
        subs = precompute_subsets(n,k); lag = precompute_lagrange(F, subs)
        cap=rho*n; john=math.sqrt(rho)*n
        interior=[x for x in range(1,n) if cap<x<john]
        ok=True
        for _ in range(15):
            w=[rng.randrange(q) for _ in range(n)]
            for a in interior:
                fast=list_count_fast(w,a,F,subs,lag)
                slow=list_size_exact(w,a,F.sub,q,k)
                if fast!=slow:
                    print(f"MISMATCH q={q} n={n} a={a}: fast={fast} slow={slow}"); ok=False
        print(f"q={q} n={n} rho={rho} interior={interior}: selftest {'OK' if ok else 'FAIL'}")

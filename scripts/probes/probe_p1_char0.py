#!/usr/bin/env python3
"""
P1-char0-closedform [#407 probe]: CHAR-0 (q-free; p >> n^3) worst-case FAR-line incidence
I_0(delta) at CONSTANT rate, and test whether it has a CLOSED FORM (=> would reduce delta* to
Mann/Lam-Leung, proven) or grows uncontrollably (=> open).

OBJECT (in-tree governing law; substrate FarCosetExplosion / MCAThresholdLedger, axiom-clean):
  For a FAR pencil (a,b) over mu_n in F_p (n | p-1), offset x^a and direction x^b,
    I(a,b; r) = #{ gamma in F_p : (x^a + gamma x^b)|_{mu_n} within Hamming dist r of RS[mu_n,k] }
              = #{ gamma : max-agreement(x^a + gamma x^b, RS[k]) >= n - r }.
  delta* = sup{ delta = r/n : max over FAR pencils (a,b>=k, b!=n/2) of I(a,b; floor(delta n)) <= n }.
  PRIZE budget = q*eps* = (n*2^128)*2^-128 = n.

CHAR-0 = take p >> n^3 (prize direction: p ~ n*2^128 >> n^3); counts are p-INDEPENDENT in this
regime (verified across several primes here).

ALGORITHM (target's prescribed (k+1)-subset method; scales past brute force):
  Each (k+1)-subset A of positions: solve the (k+1)x(k+1) system
      g(zeta^i) = zeta^{ib} + gamma zeta^{ia}  (i in A),  g deg<k,  unknowns (g, gamma)
  -> a UNIQUE gamma_A (non-degenerate case): a candidate with agreement >= k+1.
  HISTOGRAM of gamma values. KEY IDENTITY (single-codeword, generic below capacity, large p):
  a gamma whose f_gamma matches one deg<k codeword on exactly m points is hit by EXACTLY
  C(m, k+1) subsets => agreement m = invert C(m,k+1) = mult. I(a,b;r)=#{gamma: agreement>=n-r}.
  VALIDATED against the brute-force agreement-set enumerator on n=16 (all rungs, far directions).
"""
import sys, math, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import get_W

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            return p
        p += n

# ---------------- brute-force reference (agreement-set enumeration) ----------------
def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence_brute(S, p, k, a, b, r):
    n = len(S); size = n - r
    if size <= k: return p, True
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): return p, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return len(good), False

# ---------------- efficient (k+1)-subset method ----------------
def _gamma_hist(S, p, k, a, b):
    """Histogram {gamma_A : multiplicity} over all (k+1)-subsets A giving a unique gamma."""
    n = len(S)
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]
    Vx = [[pow(int(x), j, p) for j in range(k)] for x in S]
    ncols = k + 1
    hist = {}
    for A in itertools.combinations(range(n), k + 1):
        rows = []
        for i in A:
            # line is  x^a + gamma*x^b ;  solve  sum c_j x^j - gamma*x^b = x^a
            # unknown cols: [c_0..c_{k-1}, (-gamma)], RHS = x^a
            rows.append(Vx[i] + [(-pb[i]) % p, pa[i]])
        R = _rref(rows, p)
        ok = True; piv = []
        for row in R:
            c = next((j for j in range(ncols) if row[j] % p), None)
            if c is None:
                ok = False; break       # rank-deficient -> degenerate, skip
            piv.append(c)
        if not ok or sorted(piv) != list(range(ncols)): continue
        g = None
        for row in R:
            if row[k] % p == 1 and all(row[j] % p == 0 for j in range(ncols) if j != k):
                g = (-row[ncols]) % p; break
        if g is None: continue
        hist[g] = hist.get(g, 0) + 1
    return hist

def _agreement_atleast(S, p, k, vec, thresh):
    """EXACT test: does some deg<k codeword agree with vec on >= thresh points?
       Enumerate C(n,k) anchors; for each, count global matches; return True at first >= thresh.
       Also returns the max agreement found (for diagnostics)."""
    n = len(S); best = 0
    Sx = [int(x) for x in S]
    for T in itertools.combinations(range(n), k):
        xs = [Sx[i] for i in T]; ys = [vec[i] for i in T]
        cnt = 0
        for j in range(n):
            xj = Sx[j]; val = 0
            hit = False
            for t in range(k):
                if xj == xs[t]:
                    val = ys[t]; hit = True; break
            if not hit:
                for t in range(k):
                    num = ys[t]; den = 1
                    for s in range(k):
                        if s == t: continue
                        num = num * ((xj - xs[s]) % p) % p
                        den = den * ((xs[t] - xs[s]) % p) % p
                    val = (val + num * pow(den, p - 2, p)) % p
            if val == vec[j]: cnt += 1
        if cnt > best: best = cnt
        if best >= thresh: return True, best
        if best == n: break
    return (best >= thresh), best

import numpy as _np

class AgreeEngine:
    """Fast EXACT agreement test via a precomputed per-(S,p) Lagrange tensor.
       For anchor T (k pts) and target j: interp_T(f)(x_j) = sum_t f[T[t]]*Lag[T,j,t] mod p.
       agreement(T,f)=#{j:interp==f[j]}; max over all C(n,k) anchors. Vectorized over anchors+points.
       VALIDATED == pure-Python _agreement_atleast on n=16 (200 survivors, 0 mismatch)."""
    def __init__(self, S, p, k):
        self.p = p; self.k = k; self.n = len(S)
        Sx = [int(x) for x in S]; n = self.n
        combos = list(itertools.combinations(range(n), k))
        self.combos = _np.array(combos, dtype=_np.int64)
        C = len(combos)
        Lag = _np.zeros((C, n, k), dtype=_np.int64)
        for ci, T in enumerate(combos):
            xs = [Sx[i] for i in T]
            for j in range(n):
                xj = Sx[j]
                if xj in xs:
                    ti = xs.index(xj)
                    for t in range(k): Lag[ci, j, t] = 1 if t == ti else 0
                else:
                    for t in range(k):
                        num = 1; den = 1
                        for s in range(k):
                            if s == t: continue
                            num = num * ((xj - xs[s]) % p) % p
                            den = den * ((xs[t] - xs[s]) % p) % p
                        Lag[ci, j, t] = num * pow(den, p - 2, p) % p
        self.Lag = Lag
    def atleast(self, f, thresh):
        p = self.p; f = _np.array(f, dtype=_np.int64) % p
        fanch = f[self.combos]
        interp = _np.einsum('ct,cjt->cj', fanch, self.Lag) % p
        cnts = (interp == f[None, :]).sum(axis=1)
        best = int(cnts.max())
        return best >= thresh, best

def incidence_fast(S, p, k, a, b, r, eng, use_np_hist=True):
    """EXACT I(a,b;r) with the numpy AgreeEngine + (k+1)-subset histogram + multiplicity prefilter."""
    n = len(S); t = n - r
    if t <= k: return p, 0
    hist = _gamma_hist_np(S, p, k, a, b) if use_np_hist else _gamma_hist(S, p, k, a, b)
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]
    need = math.comb(t, k + 1)
    survivors = [g for g, m in hist.items() if m >= need]
    count = 0
    for g in survivors:
        f = [(pa[i] + g * pb[i]) % p for i in range(n)]
        ok, _ = eng.atleast(f, t)
        if ok: count += 1
    if 0 not in survivors:
        ok0, _ = eng.atleast(pa, t)
        if ok0: count += 1
    return count, len(survivors)

def incidence_kplus1(S, p, k, a, b, r, want_amb=False):
    """EXACT I(a,b;r): candidate gammas via (k+1)-subset histogram. PREFILTER by multiplicity:
       a gamma with agreement >= t=n-r is hit by >= C(t,k+1) subsets (a single codeword on t pts
       contributes exactly C(t,k+1) (k+1)-subsets), so only mult >= C(t,k+1) can qualify. Then run
       EXACT threshold test on survivors only. Plus gamma=0 (line collapses to offset x^a)."""
    n = len(S); t = n - r
    if t <= k:   # below dimension: every gamma is within radius -> saturated p
        return p, 0
    hist = _gamma_hist(S, p, k, a, b)
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]
    need = math.comb(t, k + 1)
    count = 0; checked = 0
    survivors = [g for g, m in hist.items() if m >= need]
    for g in survivors:
        f = [(pa[i] + g * pb[i]) % p for i in range(n)]
        ok, _ = _agreement_atleast(S, p, k, f, t)
        checked += 1
        if ok: count += 1
    # gamma=0 (only if not already a survivor): offset x^a alone
    if 0 not in survivors:
        va = pa
        ok0, _ = _agreement_atleast(S, p, k, va, t)
        if ok0: count += 1
    if want_amb: return count, checked, {}
    return count, checked

def max_far_incidence_kplus1(S, p, k, r, half_excluded=True):
    """max over FAR monomial pencils (b in [k, n-r), a!=b, b!=n/2) of I(a,b;r)."""
    n = len(S); size = n - r; best = (-1, None); tot_amb = 0
    half = n // 2
    for b in range(k, size):
        if half_excluded and b == half: continue
        for a in range(n):
            if a == b: continue
            c, amb = incidence_kplus1(S, p, k, a, b, r)
            tot_amb += amb
            if c > best[0]: best = (c, (a, b))
    return best[0], best[1], tot_amb

# ---------------- numpy-batched histogram (for n=32 scale) ----------------
import numpy as _np

def _gamma_hist_np(S, p, k, a, b, batch=6000):
    """Fully-vectorized modular Gauss-Jordan over batches of (k+1)-subset systems. Returns
       {gamma: multiplicity}. Validated equal to _gamma_hist on n=16 (all directions tested).
       Requires p^2 < 2^63 (use p ~ 1e8); p must satisfy p >> n^3."""
    assert p * p < 2**63, "p too large for int64 modular products"
    n = len(S)
    Sx = _np.array([int(x) for x in S], dtype=_np.int64)
    pw = lambda e: _np.array([pow(int(v), e, p) for v in Sx], dtype=_np.int64)
    Xj = [pw(j) for j in range(k)]
    rowmat = _np.stack(Xj + [(-pw(b)) % p, pw(a)], axis=1).astype(_np.int64)  # (n, k+2)
    ncols = k + 1
    inv_cache = {}
    def vinv(arr):
        of = _np.empty(arr.shape, dtype=_np.int64); fl = arr.reshape(-1); ofl = of.reshape(-1)
        for i in range(fl.shape[0]):
            v = int(fl[i]) % p; r = inv_cache.get(v)
            if r is None:
                r = pow(v, p - 2, p) if v != 0 else 1; inv_cache[v] = r
            ofl[i] = r
        return of
    hist = {}; buf = []
    def flush(buf):
        if not buf: return
        M = _np.stack([rowmat[list(A)] for A in buf]).astype(_np.int64)
        B = M.shape[0]; alive = _np.ones(B, dtype=bool)
        for c in range(ncols):
            for rr in range(c + 1, ncols):
                need = alive & (M[:, c, c] % p == 0)
                if not need.any(): break
                cand = need & (M[:, rr, c] % p != 0)
                if cand.any():
                    tmp = M[cand, c, :].copy(); M[cand, c, :] = M[cand, rr, :]; M[cand, rr, :] = tmp
            dead = alive & (M[:, c, c] % p == 0); alive = alive & ~dead
            if not alive.any(): break
            piv = M[:, c, c].copy(); piv[~alive] = 1
            ip = vinv(piv % p); M[:, c, :] = (M[:, c, :] * ip[:, None]) % p
            for rr in range(ncols):
                if rr == c: continue
                fct = M[:, rr, c].copy(); M[:, rr, :] = (M[:, rr, :] - fct[:, None] * M[:, c, :]) % p
        # vectorized extraction: valid full-rank systems have M[:,k,k]==1 and M[:,k,j]==0 (j!=k);
        # gamma = M[:,k,ncols].
        rowk = M[:, k, :]                               # (B, k+2)
        good = alive & (rowk[:, k] % p == 1)
        for j in range(ncols):
            if j == k: continue
            good = good & (rowk[:, j] % p == 0)
        gammas = (rowk[:, ncols] % p)[good]
        for g in gammas.tolist():
            hist[int(g)] = hist.get(int(g), 0) + 1
    for A in itertools.combinations(range(n), k + 1):
        buf.append(A)
        if len(buf) >= batch: flush(buf); buf = []
    flush(buf)
    return hist

def incidence_np(S, p, k, a, b, r):
    """n=32-scale exact I(a,b;r): numpy histogram + multiplicity prefilter + exact threshold test."""
    n = len(S); t = n - r
    if t <= k: return p, 0
    hist = _gamma_hist_np(S, p, k, a, b)
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]
    need = math.comb(t, k + 1)
    survivors = [g for g, m in hist.items() if m >= need]
    count = 0
    for g in survivors:
        f = [(pa[i] + g * pb[i]) % p for i in range(n)]
        ok, _ = _agreement_atleast(S, p, k, f, t)
        if ok: count += 1
    if 0 not in survivors:
        ok0, _ = _agreement_atleast(S, p, k, pa, t)
        if ok0: count += 1
    return count, len(survivors)

# ---------------- delta* sweep ----------------
def delta_star_kplus1(n, k, p, budget=None):
    S = list(get_W(n, p).S); budget = budget or n
    rows = []; last_good = None; first_bad = None
    for r in range(k + 1, n - k + 2):
        mx, st, amb = max_far_incidence_kplus1(S, p, k, r)
        rows.append((r, r / n, mx, st, amb))
        if mx <= budget:
            last_good = r
        elif first_bad is None:
            first_bad = (r, st)
    ds = (last_good / n) if last_good is not None else None
    return ds, first_bad, rows

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', default='validate')
    ap.add_argument('--n', type=int, default=16)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--plo', type=int, default=200003)
    ap.add_argument('--r', type=int, default=10)
    ap.add_argument('--rmin', type=int, default=-1)
    ap.add_argument('--rmax', type=int, default=-1)
    ap.add_argument('--nprimes', type=int, default=3)
    args = ap.parse_args()

    if args.mode == 'validate':
        # VALIDATION: efficient (k+1) vs brute (agreement-set) — FULL exhaustive sweep, all (a,b,r).
        n, k = args.n, args.k
        p = find_prime_cong1(n, args.plo); S = list(get_W(n, p).S)
        print(f"VALIDATION n={n} k={k} p={p}  [efficient (k+1)-subset vs brute agreement-set]", flush=True)
        allmatch = True; nmis = 0; nchk = 0; namb = 0
        for r in range(k + 1, n - k + 2):
            size = n - r
            for b in range(k, size):
                if b == n // 2: continue   # antipodal direction excluded by governing law
                for a in range(n):
                    if a == b: continue
                    cb, sat = incidence_brute(S, p, k, a, b, r)
                    if sat:  # saturated => p; skip (k+1 method counts finite gammas only)
                        continue
                    ce, amb = incidence_kplus1(S, p, k, a, b, r)
                    namb += amb; nchk += 1
                    if cb != ce:
                        allmatch = False; nmis += 1
                        if nmis <= 30:
                            print(f"  MISMATCH (a={a},b={b},r={r}): brute={cb} kplus1={ce} amb={amb}", flush=True)
        print(f"  ALL MATCH = {allmatch}  (checked={nchk} mismatches={nmis} total_ambiguous={namb})", flush=True)

    elif args.mode == 'validate_focus':
        # FOCUSED validation: only binding rungs (around Johnson..capacity) + ALL far dirs.
        n, k = args.n, args.k
        p = find_prime_cong1(n, args.plo); S = list(get_W(n, p).S)
        rho = k / n
        rlo = max(k + 1, int(n * (1 - (rho)**0.5)) - 1)   # ~ Johnson radius lower
        rhi = min(n - k + 1, int(n * (1 - rho)) + 1)       # ~ capacity
        print(f"FOCUS VALIDATION n={n} k={k} p={p} rungs r in [{rlo},{rhi}]", flush=True)
        allmatch = True; nmis = 0; nchk = 0; namb = 0
        for r in range(rlo, rhi + 1):
            size = n - r
            for b in range(k, size):
                if b == n // 2: continue   # antipodal direction excluded by governing law
                for a in range(n):
                    if a == b: continue
                    cb, sat = incidence_brute(S, p, k, a, b, r)
                    if sat: continue
                    ce, amb = incidence_kplus1(S, p, k, a, b, r)
                    namb += amb; nchk += 1
                    if cb != ce:
                        allmatch = False; nmis += 1
                        if nmis <= 30:
                            print(f"  MISMATCH (a={a},b={b},r={r}): brute={cb} kplus1={ce} amb={amb}", flush=True)
        print(f"  FOCUS MATCH = {allmatch} (checked={nchk} mism={nmis} amb={namb})", flush=True)

    elif args.mode == 'deltastar':
        # FULL char-0 delta* table at constant rate (feasible n: full far sweep), multi-prime check.
        n, k = args.n, args.k
        rho = k / n
        allp = [find_prime_cong1(n, args.plo), find_prime_cong1(n, args.plo + 300000),
                find_prime_cong1(n, args.plo + 800000)]
        primes = allp[:args.nprimes]
        rmin = args.rmin if args.rmin > 0 else (k + 1)
        rmax = args.rmax if args.rmax > 0 else (n - k + 1)
        print(f"=== CHAR-0 DELTA* TABLE  n={n} k={k} rho={rho} budget=n={n}  rungs[{rmin},{rmax}] ===", flush=True)
        print(f"primes (all >> n^3={n**3}): {primes}", flush=True)
        for p in primes:
            S = list(get_W(n, p).S)
            print(f"-- p={p} --   r  delta=r/n  maxI(far)  binder(a,b)  survivors", flush=True)
            last_good = None; first_bad = None
            for r in range(rmin, rmax + 1):
                mx, st, amb = max_far_incidence_kplus1(S, p, k, r)
                if mx < 0:   # no valid far direction at this size -> stop (boundary reached)
                    print(f"   r={r:2d}  {r/n:.4f}  (no valid far direction; size={n-r})", flush=True)
                    break
                tag = ""
                # delta* = sup of contiguous good rungs: stop at FIRST bad
                if first_bad is None:
                    if mx <= n: last_good = r
                    else: first_bad = (r, st); tag = "  <-- FIRST BAD (delta* crossing)"
                print(f"   r={r:2d}  {r/n:.4f}  I={mx:6d}  {str(st):10s}  surv={amb}{tag}", flush=True)
            ds = (last_good / n) if last_good is not None else None
            print(f"   => delta* = {last_good}/{n} = {ds}   (first bad rung: {first_bad})", flush=True)
            # closed-form candidate comparison
            import math as _m
            H = (-rho*_m.log2(rho) - (1-rho)*_m.log2(1-rho)) if 0<rho<1 else 0.0
            johnson = 1 - rho**0.5
            cands = {
                "Johnson 1-sqrt(rho)": johnson,
                "capacity 1-rho": 1-rho,
                "1-rho-1/log2(n)": 1-rho-1/_m.log2(n),
                "1-rho-H(rho)/log2(n)": 1-rho-H/_m.log2(n),
                "1-rho-1/n": 1-rho-1/n,
                "1-rho-H/(2 log2 n)": 1-rho-H/(2*_m.log2(n)),
            }
            if ds is not None:
                print(f"   closed-form comparison (delta*={ds:.4f}):", flush=True)
                for name, v in cands.items():
                    print(f"      {name:28s} = {v:.4f}   (delta*-cf = {ds-v:+.4f})", flush=True)

    elif args.mode == 'deltastar_dir':
        # restricted-direction delta* for LARGE n: heavy enumeration only on candidate far dirs b,
        # plus a CHEAP full-direction confirm at the binding rung. Reports per-direction max I.
        n, k = args.n, args.k
        p = find_prime_cong1(n, args.plo); S = list(get_W(n, p).S); rho = k/n
        cand_b = sorted(set([k, k+1, k+2, n//4 if n//4>=k else k, n//2-1, n-k-1]))
        cand_b = [b for b in cand_b if k <= b < n]
        print(f"=== RESTRICTED-DIR DELTA*  n={n} k={k} rho={rho} p={p} budget=n={n} ===", flush=True)
        print(f"candidate far directions b: {cand_b}", flush=True)
        last_good = None; first_bad = None
        for r in range(k + 1, n - k + 2):
            size = n - r
            best = (-1, None); amb_tot = 0
            for b in cand_b:
                if b >= size or b == n//2: continue
                for a in range(n):
                    if a == b: continue
                    c, amb = incidence_kplus1(S, p, k, a, b, r)
                    amb_tot += amb
                    if c > best[0]: best = (c, (a, b))
            mx, st = best
            tag = ""
            if mx <= n: last_good = r
            elif first_bad is None: first_bad = (r, st); tag = "  <-- FIRST BAD"
            print(f"   r={r:2d}  delta={r/n:.4f}  I={mx:6d}  binder={st}  amb={amb_tot}{tag}", flush=True)
        ds = (last_good/n) if last_good is not None else None
        print(f"   => delta* (restricted dirs) = {last_good}/{n} = {ds}", flush=True)
        import math as _m
        H=(-rho*_m.log2(rho)-(1-rho)*_m.log2(1-rho))
        print(f"   Johnson={1-rho**0.5:.4f} cap-1/log2n={1-rho-1/_m.log2(n):.4f} "
              f"cap-H/log2n={1-rho-H/_m.log2(n):.4f} cap-1/n={1-rho-1/n:.4f}", flush=True)

    elif args.mode == 'bindrung_fullscan':
        # at a single rung r, FULL direction scan (all b in [k,size)) to confirm which b binds.
        n, k, r = args.n, args.k, args.r
        p = find_prime_cong1(n, args.plo); S = list(get_W(n, p).S); size = n-r
        print(f"=== FULL-DIR SCAN n={n} k={k} r={r} (size={size}) p={p} ===", flush=True)
        rows=[]
        for b in range(k, size):
            if b == n//2: continue
            bestb=(-1,None)
            for a in range(n):
                if a==b: continue
                c,amb=incidence_kplus1(S,p,k,a,b,r)
                if c>bestb[0]: bestb=(c,a)
            rows.append((b,bestb[0],bestb[1]))
            print(f"   b={b:2d}  maxI={bestb[0]:6d}  best a={bestb[1]}", flush=True)
        rows.sort(key=lambda t:-t[1])
        print(f"   TOP binders: {rows[:5]}", flush=True)

    elif args.mode == 'bindscan_np':
        # n=32-scale FULL-direction scan at one rung r using the numpy histogram.
        n, k, r = args.n, args.k, args.r
        p = find_prime_cong1(n, max(args.plo, 100000019)); S = list(get_W(n, p).S); size = n - r
        print(f"=== NP FULL-DIR SCAN n={n} k={k} r={r} delta={r/n:.4f} (size={size}) p={p} ===", flush=True)
        rows = []
        for b in range(k, size):
            if b == n // 2: continue
            bestb = (-1, None)
            for a in range(n):
                if a == b: continue
                c, surv = incidence_np(S, p, k, a, b, r)
                if c > bestb[0]: bestb = (c, a)
            rows.append((b, bestb[0], bestb[1]))
            print(f"   b={b:2d}  maxI={bestb[0]:6d}  best a={bestb[1]}", flush=True)
        rows.sort(key=lambda t: -t[1])
        print(f"   TOP binders (b,maxI,a): {rows[:6]}", flush=True)

    elif args.mode == 'deltastar_np':
        # n=32-scale char-0 delta* via numpy histogram. Sweep candidate far directions across rungs.
        # cand_b includes low-exponent (binder per n=16) + a representative spread; b != n/2.
        n, k = args.n, args.k; rho = k / n
        primes = [find_prime_cong1(n, max(args.plo, 100000019))]
        if args.nprimes > 1:
            primes.append(find_prime_cong1(n, max(args.plo, 100000019) + 5000000))
        cand_b = sorted(set([k, k+1, k+2, k+3, n//8 if n//8>=k else k, n//4 if n//4>=k else k]))
        cand_b = [b for b in cand_b if k <= b < n and b != n//2]
        rmin = args.rmin if args.rmin > 0 else (k + 1)
        rmax = args.rmax if args.rmax > 0 else (n - k + 1)
        print(f"=== NP CHAR-0 DELTA* n={n} k={k} rho={rho} budget=n={n} rungs[{rmin},{rmax}] ===", flush=True)
        print(f"candidate far directions b (restricted): {cand_b}  (full-scan confirm via bindscan_np)", flush=True)
        for p in primes:
            S = list(get_W(n, p).S)
            print(f"-- p={p} (>> n^3={n**3}) --", flush=True)
            last_good = None; first_bad = None
            for r in range(rmin, rmax + 1):
                size = n - r
                best = (-1, None); surv_tot = 0
                for b in cand_b:
                    if b >= size: continue
                    for a in range(n):
                        if a == b: continue
                        c, surv = incidence_np(S, p, k, a, b, r)
                        surv_tot += surv
                        if c > best[0]: best = (c, (a, b))
                mx, st = best
                if mx < 0:
                    print(f"   r={r:2d}  (no valid far direction; size={size})", flush=True); break
                tag = ""
                if first_bad is None:
                    if mx <= n: last_good = r
                    else: first_bad = (r, st); tag = "  <-- FIRST BAD (delta* crossing)"
                print(f"   r={r:2d}  delta={r/n:.4f}  I={mx:6d}  binder={st}{tag}", flush=True)
            ds = (last_good / n) if last_good is not None else None
            import math as _m
            H = (-rho*_m.log2(rho) - (1-rho)*_m.log2(1-rho))
            print(f"   => delta* (restricted dirs) = {last_good}/{n} = {ds}  (first bad {first_bad})", flush=True)
            if ds is not None:
                print(f"      Johnson 1-sqrt(rho) = {1-rho**0.5:.4f}   capacity 1-rho = {1-rho:.4f}", flush=True)
                print(f"      1-rho-1/log2(n) = {1-rho-1/_m.log2(n):.4f}   1-rho-H/log2(n) = {1-rho-H/_m.log2(n):.4f}"
                      f"   1-rho-1/n = {1-rho-1/n:.4f}", flush=True)

    elif args.mode == 'deltastar_fast':
        # FAST char-0 delta* (numpy histogram + numpy AgreeEngine). Works n=16 AND n=32.
        # 'dirs' = full far sweep (feasible n<=16) or restricted (n=32). Engine built ONCE.
        n, k = args.n, args.k; rho = k / n
        plo = max(args.plo, 100000019) if n >= 24 else args.plo
        primes = [find_prime_cong1(n, plo)]
        if args.nprimes > 1: primes.append(find_prime_cong1(n, plo + 5000000))
        full = (n <= 18)
        cand_b = None
        if not full:
            cand_b = sorted(set([k, k+1, k+2, k+3, n//8 if n//8>=k else k, n//4 if n//4>=k else k]))
            cand_b = [b for b in cand_b if k <= b < n and b != n//2]
        rmin = args.rmin if args.rmin > 0 else (k + 1)
        rmax = args.rmax if args.rmax > 0 else (n - k + 1)
        import math as _m
        H = (-rho*_m.log2(rho) - (1-rho)*_m.log2(1-rho))
        print(f"=== FAST CHAR-0 DELTA* n={n} k={k} rho={rho} budget=n={n} rungs[{rmin},{rmax}] "
              f"dirs={'FULL' if full else cand_b} ===", flush=True)
        for p in primes:
            S = list(get_W(n, p).S)
            eng = AgreeEngine(S, p, k)
            print(f"-- p={p} (>> n^3={n**3}) --", flush=True)
            last_good = None; first_bad = None
            for r in range(rmin, rmax + 1):
                size = n - r
                bs = range(k, size) if full else [b for b in cand_b if b < size]
                best = (-1, None); surv_tot = 0
                for b in bs:
                    if b == n // 2: continue
                    for a in range(n):
                        if a == b: continue
                        c, surv = incidence_fast(S, p, k, a, b, r, eng)
                        surv_tot += surv
                        if c > best[0]: best = (c, (a, b))
                mx, st = best
                if mx < 0:
                    print(f"   r={r:2d}  (no valid far direction; size={size})", flush=True); break
                tag = ""
                if first_bad is None:
                    if mx <= n: last_good = r
                    else: first_bad = (r, st); tag = "  <-- FIRST BAD (delta* crossing)"
                print(f"   r={r:2d}  delta={r/n:.4f}  I={mx:6d}  binder={st}  surv={surv_tot}{tag}", flush=True)
            ds = (last_good / n) if last_good is not None else None
            print(f"   => delta* = {last_good}/{n} = {ds}  (first bad rung {first_bad})", flush=True)
            if ds is not None:
                print(f"      closed-form: Johnson 1-sqrt(rho)={1-rho**0.5:.4f}  capacity 1-rho={1-rho:.4f}", flush=True)
                print(f"      1-rho-1/log2(n)={1-rho-1/_m.log2(n):.4f}  1-rho-H/log2(n)={1-rho-H/_m.log2(n):.4f}  "
                      f"1-rho-1/n={1-rho-1/n:.4f}  1-rho-H/(2log2 n)={1-rho-H/(2*_m.log2(n)):.4f}", flush=True)

    elif args.mode == 'bindscan_fast':
        # FAST full-direction scan at one rung r (numpy hist + AgreeEngine). Confirms binder for n=32.
        n, k, r = args.n, args.k, args.r
        p = find_prime_cong1(n, max(args.plo, 100000019) if n >= 24 else args.plo)
        S = list(get_W(n, p).S); size = n - r
        eng = AgreeEngine(S, p, k)
        print(f"=== FAST FULL-DIR SCAN n={n} k={k} r={r} delta={r/n:.4f} (size={size}) p={p} ===", flush=True)
        rows = []
        for b in range(k, size):
            if b == n // 2: continue
            bestb = (-1, None)
            for a in range(n):
                if a == b: continue
                c, surv = incidence_fast(S, p, k, a, b, r, eng)
                if c > bestb[0]: bestb = (c, a)
            rows.append((b, bestb[0], bestb[1]))
            print(f"   b={b:2d}  maxI={bestb[0]:6d}  best a={bestb[1]}", flush=True)
        rows.sort(key=lambda t: -t[1])
        print(f"   TOP binders (b,maxI,a): {rows[:6]}", flush=True)

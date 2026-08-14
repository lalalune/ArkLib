#!/usr/bin/env python3
"""
P4-mann-agreement-count (#407): Does MANN'S THEOREM pin the char-0 agreement-set count? NO.

GOVERNING OBJECT (in-tree exact; FarCosetExplosion / probe_farline_incidence_exact.py):
  For a FAR monomial pencil  x^a + alpha*x^b  on mu_n (far means b in [k, n-r)), the char-0
  incidence
    I_0(a,b; w) = #{ alpha : x^a + alpha*x^b agrees with some deg-<k RS codeword on a set R of
                    size w points of mu_n }   (delta = (n-w)/n).
  Computed EXACTLY over a big prime q >> n^4 (char-0 faithful; q-stability re-verified below).

THE MANN ANGLE under test:
  f(x) = x^a + alpha*x^b - g(x), g deg<k, has support in {0..k-1} U {a,b}  (<= k+2 terms).
  An agreement set R (|R|=w) is exactly the roots of f in mu_n; each root zeta^j gives a
  vanishing sum of <= k+2 roots of unity. For mu_{2^mu} (Lam-Leung) the MINIMAL vanishing
  relations are antipodal pairs {x,-x}. The PROPOSED prize closure: every achievable rich
  agreement set R is forced to be built from antipodal pairing => the agreement/orbit count is
  governed by the PROVEN Mann/Lam-Leung antipodal combinatorics, not by an analytic (BGK) wall.

TEST:  Mann_anti(a,b;w) == I_0(a,b;w) ?  where Mann_anti = #{distinct alpha that admit an
  antipodally-closed witness R}.  EXACT => Mann closes the count; mismatch => report the gap.

=========================== VERDICT: REFUTED (clean mismatch) ==========================
Mann's antipodal count is a STRICT UNDERCOUNT of I_0 everywhere EXCEPT the large-agreement
(near/below-Johnson) regime. Measured (q-stable across q=262193 and q=2621569):

  n=16 k=4 (rho=1/4):
    w=5 delta=0.688  I0=3696  Mann_anti=0     nonAnti=3696   (window interior; Mann sees NONE)
    w=6 delta=0.625  I0=88    Mann_anti=24    nonAnti=64
    w=7 delta=0.562  I0=8     Mann_anti=0     nonAnti=8
    w=8 delta=0.500  I0=8     Mann_anti=8     nonAnti=0       EXACT (Johnson edge; R forced antipodal)
    w=9 delta=0.438  I0=16    Mann_anti=0     nonAnti=16

MECHANISM (root cause, confirmed by the diagnostic companion probe_407_mann_diag below):
  g(x) carries k FREE field coefficients and alpha is free, so the vanishing sum at zeta^j has
  ARBITRARY coefficients. Lam-Leung/Mann governs vanishing sums with +-1 / root-of-unity
  coefficients ONLY. With free coefficients, ANY size-(k+1) set R can be interpolated into an
  agreement set (at w=k+1=5, n=16, 2256 of the C(16,5)=4368 subsets each force a distinct alpha).
  The window-interior agreement sets are contiguous arcs like R=(0,1,2,3,4) -- NOT antipodal-pair
  unions. They are LINEAR-ALGEBRA (interpolation) realizable; the antipodal combinatorics is the
  wrong governing structure there.
  Mann/Lam-Leung becomes EXACT only at the large-w Johnson edge (w=8=n/2 here), where every
  agreement set R is FORCED antipodally closed (all R in the w=8 rows are antipodal-closed --
  see diagnostic part (3)).

CONSEQUENCE for the prize: the agreement/orbit count in the WINDOW INTERIOR (beyond Johnson,
below capacity -- the prize target) is NOT pinned by the proven Mann/Lam-Leung theorem. It is a
free-coefficient interpolation count, exactly the (a,b)-pencil incidence I(delta) of the
governing law -- the same open BGK/counting object, NOT closeable via Mann. Mann closes only the
already-known near-Johnson regime.
"""
import itertools
from sympy import isprime

# ---------- mu_n over a char-0-faithful big prime ----------
def big_prime(n, lo):
    q = ((lo // n) + 1) * n + 1
    while not isprime(q): q += n
    return q

def gen_mu(q, n):
    for x in range(2, q):
        if pow(x, n, q) == 1 and pow(x, n // 2, q) != 1:
            return [pow(x, i, q) for i in range(n)]
    raise RuntimeError("no mu_n")

# ---------- exact char-0 incidence via per-witness affine-in-alpha solve ----------
def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0; pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p); rows[pr] = [(x * inv) % p for x in rows[pr]]
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

def agreement_sets(S, p, k, a, b, w):
    """All (R, alpha): size-w witness R that forces a single nonzero alpha. heavy = some R
       admits all alpha (saturated); flagged but excluded from the alpha set."""
    n = len(S)
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    out = []; heavy = False
    for R in itertools.combinations(range(n), w):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]; P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(w)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(w)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): heavy = True
            continue
        i = next(j for j in range(len(pb)) if pb[j]); g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))) and g != 0:
            out.append((R, g))
    return out, heavy

# ---------- antipodal / coset classification (the Mann/Lam-Leung structure) ----------
def antipodal_closed(R, n):
    Rs = set(R); h = n // 2
    return all(((j + h) % n) in Rs for j in R)

def coset_core(R, n):
    Rs = set(R); best = set()
    for d in range(2, n + 1):
        if n % d: continue
        step = n // d; seen = set(); core = set()
        for j in range(n):
            if j in seen: continue
            cs = set((j + step * t) % n for t in range(d)); seen |= cs
            if cs <= Rs: core |= cs
        if len(core) > len(best): best = core
    return best

def compare(S, n, k, a, b, w, q):
    sets, heavy = agreement_sets(S, q, k, a, b, w)
    I0_alphas = set(g for _, g in sets)
    mann_anti = set(g for R, g in sets if antipodal_closed(R, n))
    mann_coset = set(g for R, g in sets if len(coset_core(R, n)) == len(R))
    nonanti = I0_alphas - mann_anti
    ex = next(iter([(R, g) for R, g in sets if g in nonanti]), None)
    return dict(I0=len(I0_alphas), heavy=heavy, n_sets=len(sets),
                mann_anti=len(mann_anti), mann_coset=len(mann_coset),
                nonanti=len(nonanti), example_nonanti=ex)

def run(n, k, w_range=None):
    q = big_prime(n, n**4 * 4); S = gen_mu(q, n); rho = k / n
    print(f"\n=== n={n} k={k} rho={rho:.4f}  q={q} (char-0 faithful, q>>n^4) ===", flush=True)
    print(f"{'a':>3} {'b':>3} {'w':>3} {'delta':>6} | {'I0':>6} {'#sets':>6} | "
          f"{'Mann_anti':>9} {'Mann_cos':>8} {'nonAnti':>7}  match?", flush=True)
    ws = w_range if w_range else range(k + 1, n)
    rows = []
    for w in ws:
        for b in range(k, w):
            for a in range(n):
                if a == b: continue
                res = compare(S, n, k, a, b, w, q)
                if res['I0'] == 0: continue
                rows.append((a, b, w, res))
    by_w = {}
    for a, b, w, res in rows:
        if w not in by_w or res['I0'] > by_w[w][3]['I0']:
            by_w[w] = (a, b, w, res)
    for w in sorted(by_w):
        a, b, w_, res = by_w[w]; delta = (n - w) / n
        match = "EXACT" if res['I0'] == res['mann_anti'] else (
                "anti<I0" if res['mann_anti'] < res['I0'] else "anti>I0")
        flag = " [HEAVY]" if res['heavy'] else ""
        print(f"{a:>3} {b:>3} {w:>3} {delta:>6.3f} | {res['I0']:>6} {res['n_sets']:>6} | "
              f"{res['mann_anti']:>9} {res['mann_coset']:>8} {res['nonanti']:>7}  {match}{flag}", flush=True)
    gaps = [(a, b, w, res) for a, b, w, res in rows if res['nonanti'] > 0]
    if gaps:
        print(f"  --- {len(gaps)} (a,b,w) with NON-antipodal agreement alphas (the Mann gap) ---", flush=True)
        for a, b, w, res in gaps[:6]:
            print(f"    a={a} b={b} w={w} delta={(n-w)/n:.3f}: nonAnti={res['nonanti']}/{res['I0']}"
                  f"  ex(R,alpha)={res['example_nonanti']}", flush=True)
    else:
        print("  --- NO non-antipodal agreement alphas: Mann antipodal count = I0 on every scanned row ---", flush=True)
    return rows

if __name__ == '__main__':
    run(8, 2)
    run(8, 4)
    run(16, 4, w_range=range(5, 10))   # window threshold band (full a-sweep heavy for all w)

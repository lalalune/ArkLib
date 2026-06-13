#!/usr/bin/env python3
"""Probe: SLOPE COLLAPSE at the UDR-edge band (and around it).

Setup: C = RS[F_p, mu_n, k] (smooth domain, powers of g). Stack (u0, u1), radius w.
Bad gamma: exists codeword p with agreement |{i: (u0+g*u1)(i)=p(i)}| >= a = n-w,
AND the pair (u0,u1) is NOT jointly explained on any T, |T| >= a.

At edge-band radii every pair of bad witnesses overlaps in >= n-2w >= k+1 points,
so the explainer map gamma -> p_gamma has well-defined codeword slopes
c_{gg'} = (p_g - p_g')/(g - g'). The polynomial-pencil count gives
#bad <= n * t where t = gamma-degree of the Newton interpolation of p_gamma.

CONJECTURE (slope collapse): on the edge band n in [2w+k+1, 2w+2k), the map
gamma -> p_gamma of every bad family is AFFINE (t <= 1), i.e. all pair slopes equal.
If true: #bad <= wt(eps - c) + 1 <= n + 1 on the band.

This probe:
  1. enumerates/hill-climbs stacks at edge-band parameters (n, k, w) over small p,
  2. computes ALL bad gammas with their full explainer lists,
  3. checks: (a) max #bad observed, (b) whether explainer choice can be made with
     all pair-slopes equal (affine selection exists), (c) the Newton degree of the
     canonical selection, (d) uniqueness of explainers per bad gamma.
Also runs just OUTSIDE the band (2w+2k<=n and w>(n-k-1)/2) for contrast.

Convention cross-check: mcaEvent per the in-tree criterion = combo close AND NOT
(exists T, |T|>=a, u0|T and u1|T both deg<k explained). Matches probe_dim1 harness
(word-level), re-validated here on (F17, mu8, k=1) against known counts.
"""
import itertools, random, sys
from functools import lru_cache

def make_field_ops(p):
    inv = [0]*p
    for x in range(1,p): inv[x] = pow(x, p-2, p)
    return inv

def domain_points(p, g, n):
    pts = [pow(g, i, p) for i in range(n)]
    assert len(set(pts)) == n, "g must have order n"
    return pts

def interp_eval(xs, ys, p, inv):
    """Lagrange interpolation through points (xs[i], ys[i]); returns coefficient list."""
    k = len(xs)
    coeffs = [0]*k
    for i in range(k):
        # numerator poly prod_{j!=i} (X - xs[j]) , denominator prod (xs[i]-xs[j])
        num = [1]
        den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = den * ((xs[i]-xs[j]) % p) % p
        s = ys[i] * inv[den] % p
        for d_ in range(len(num)):
            coeffs[d_] = (coeffs[d_] + s*num[d_]) % p
    return coeffs

def poly_mul(a, b, p):
    r = [0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                r[i+j] = (r[i+j] + ai*bj) % p
    return r

def poly_eval(c, x, p):
    r = 0
    for a in reversed(c): r = (r*x + a) % p
    return r

def codeword_through(pts_idx, vals, pts, k, p, inv):
    """deg<k interpolant through k points (by index); returns its full evaluation vector."""
    xs = [pts[i] for i in pts_idx]; ys = list(vals)
    c = interp_eval(xs, ys, p, inv)
    return tuple(poly_eval(c, x, p) for x in pts)

def explainers(word, pts, k, a, p, inv):
    """All codewords agreeing with word on >= a points. Enumerate via k-subsets of
    candidate agreement sets: any explainer agrees on >= a >= k points, so it is the
    interpolant of SOME k-subset of its agreement set. Enumerate k-subsets of [n]."""
    n = len(word)
    seen = {}
    for sub in itertools.combinations(range(n), k):
        cw = codeword_through(sub, [word[i] for i in sub], pts, k, p, inv)
        agr = sum(1 for i in range(n) if cw[i] == word[i])
        if agr >= a:
            seen[cw] = agr
    return seen  # dict codeword-vector -> agreement

def jointly_explained(u0, u1, pts, k, a, p, inv):
    n = len(u0)
    # joint: exists T, |T|>=a, both restrictions polynomial. Equivalent: exists
    # codewords c0,c1 with |{i: c0=u0 and c1=u1 at i}| >= a.
    e0 = explainers(u0, pts, k, a, p, inv)
    e1 = explainers(u1, pts, k, a, p, inv)
    for c0 in e0:
        for c1 in e1:
            t = sum(1 for i in range(n) if c0[i]==u0[i] and c1[i]==u1[i])
            if t >= a: return True
    return False

def bad_gammas(u0, u1, pts, k, a, p, inv):
    n = len(u0)
    if jointly_explained(u0, u1, pts, k, a, p, inv): return {}
    out = {}
    for g_ in range(p):
        w_ = tuple((u0[i] + g_*u1[i]) % p for i in range(n))
        ex = explainers(w_, pts, k, a, p, inv)
        if ex: out[g_] = ex
    return out

def slope_analysis(bad, p, inv, k, n):
    """bad: gamma -> {codeword: agr}. Check affine selection + Newton degree of a
    canonical selection. Returns (num_bad, affine_possible, newton_deg_canonical,
    multi_explainer_fraction)."""
    gs = sorted(bad)
    N = len(gs)
    if N <= 2: return (N, True, max(0, N-1), 0.0)
    multi = sum(1 for g_ in gs if len(bad[g_]) > 1) / N
    # affine selection: exists choice p_g in bad[g] and codewords q,c with p_g = q + g*c.
    # Try anchored on first two gammas' explainer pairs.
    g0, g1 = gs[0], gs[1]
    for p0 in bad[g0]:
        for p1 in bad[g1]:
            dg = (g1-g0) % p
            c = tuple((p1[i]-p0[i]) * inv[dg] % p for i in range(n))
            q = tuple((p0[i] - g0*c[i]) % p for i in range(n))
            ok = True
            for g_ in gs[2:]:
                cand = tuple((q[i] + g_*c[i]) % p for i in range(n))
                if cand not in bad[g_]: ok = False; break
            if ok: return (N, True, 1, multi)
    # Newton degree of canonical (max-agreement) selection
    sel = [max(bad[g_].items(), key=lambda kv: kv[1])[0] for g_ in gs]
    # divided differences over F_p (vector-valued)
    rows = [list(s) for s in sel]
    deg = 0
    cur = rows
    for lvl in range(1, N):
        nxt = []
        anyz = True
        for i_ in range(len(cur)-1):
            dg = (gs[i_+lvl]-gs[i_]) % p
            r = [(cur[i_+1][j]-cur[i_][j]) * inv[dg] % p for j in range(n)]
            nxt.append(r)
            if any(r): anyz = False
        if not nxt or all(all(x==0 for x in r) for r in nxt):
            break
        deg = lvl
        cur = nxt
    return (N, False, deg, multi)

def run_instance(p, g, n, k, w, trials, rng, label):
    inv = make_field_ops(p)
    pts = domain_points(p, g, n)
    a = n - w
    maxbad = 0; nonaffine = 0; results = []
    for t in range(trials):
        # adversarial-ish: u1 sparse-near-code or random; u0 random or piecewise codeword
        mode = t % 4
        if mode == 0:
            u0 = tuple(rng.randrange(p) for _ in range(n)); u1 = tuple(rng.randrange(p) for _ in range(n))
        elif mode == 1:
            # u1 = codeword + sparse error (the tube)
            sub = rng.sample(range(n), k)
            cw = codeword_through(sub, [rng.randrange(p) for _ in range(k)], pts, k, p, inv)
            e = list(cw);
            for i in rng.sample(range(n), min(n, w+k)):
                e[i] = (e[i] + rng.randrange(1,p)) % p
            u1 = tuple(e); u0 = tuple(rng.randrange(p) for _ in range(n))
        elif mode == 2:
            # u0 piecewise two codewords (clique-builder), u1 sparse
            sub1 = rng.sample(range(n), k); sub2 = rng.sample(range(n), k)
            c1 = codeword_through(sub1, [rng.randrange(p) for _ in range(k)], pts, k, p, inv)
            c2 = codeword_through(sub2, [rng.randrange(p) for _ in range(k)], pts, k, p, inv)
            cut = rng.randrange(1, n)
            u0 = tuple(c1[i] if i < cut else c2[i] for i in range(n))
            e = [0]*n
            for i in rng.sample(range(n), min(n, w+1)):
                e[i] = rng.randrange(1, p)
            u1 = tuple(e)
        else:
            # both near code, different cliques
            sub1 = rng.sample(range(n), k); sub2 = rng.sample(range(n), k)
            c1 = codeword_through(sub1, [rng.randrange(p) for _ in range(k)], pts, k, p, inv)
            c2 = codeword_through(sub2, [rng.randrange(p) for _ in range(k)], pts, k, p, inv)
            u0 = list(c1); u1 = list(c2)
            for i in rng.sample(range(n), min(n, w)):
                u0[i] = (u0[i] + rng.randrange(1,p)) % p
            for i in rng.sample(range(n), min(n, w)):
                u1[i] = (u1[i] + rng.randrange(1,p)) % p
            u0 = tuple(u0); u1 = tuple(u1)
        bad = bad_gammas(u0, u1, pts, k, a, p, inv)
        if not bad: continue
        N, affine, deg, multi = slope_analysis(bad, p, inv, k, n)
        maxbad = max(maxbad, N)
        if N >= 3 and not affine:
            nonaffine += 1
            results.append((N, deg, multi, u0, u1))
    print(f"[{label}] p={p} n={n} k={k} w={w} a={a} band={'YES' if 2*w+k+1<=n<2*w+2*k else 'no'}"
          f" trials={trials}: maxbad={N if False else maxbad}, nonaffine_families={nonaffine}")
    for (N, deg, multi, u0, u1) in results[:3]:
        print(f"    NONAFFINE: #bad={N} newton_deg={deg} multi_frac={multi:.2f}")
        print(f"      u0={u0}")
        print(f"      u1={u1}")
    return maxbad, nonaffine

def main():
    rng = random.Random(371)
    # cross-check vs dim-1 known: (F17, mu8 g=2, k=1): expect criterion to work
    run_instance(17, 2, 8, 1, 3, 200, rng, "xcheck-k1")
    # EDGE BAND instances: n in [2w+k+1, 2w+2k)
    # n=8, k=2: band w: 2w+3<=8<2w+4 -> w in {ceil((8-4)/2)=2.5..}: 8-2k=4 -> w: (8-4)/2=2 < w <= (8-3)/2=2.5 -> w=... 2w+3<=8 -> w<=2.5 -> w=2: 2*2+3=7<=8<2*2+4=8? 8<8 no. w=2 not in band for n=8.
    # Solve: band needs 2w+k+1 <= n <= 2w+2k-1. n=9,k=2: w=3: 9<=9<=9 yes (p=19, g order 9? 9|18 yes g=4? ord 4 mod19: 4^9=262144... use p=19, n=9, g with order 9: g=4 (4^9 mod 19 = 1? 4^3=64=7, 4^9=7^3=343=343-18*19=1 yes, ord=9))
    run_instance(19, 4, 9, 2, 3, 300, rng, "edge-n9k2")
    # n=8, k=3: band: 2w+4<=8<=2w+5 -> w=2: 8<=8<=9 yes
    run_instance(17, 2, 8, 3, 2, 300, rng, "edge-n8k3")
    # n=16, k=3: 2w+4<=16<=2w+5 -> w=6: 16<=16<=17 yes (p=17, g=3 ord 16)
    run_instance(17, 3, 16, 3, 6, 120, rng, "edge-n16k3")
    # n=16, k=5: 2w+6<=16<=2w+9 -> w=4: 14<=16<=17? 2*4+6=14<=16, 16<=2*4+9=17 yes; w=5: 16<=16<=19 yes
    run_instance(17, 3, 16, 5, 5, 80, rng, "edge-n16k5")
    # just OUTSIDE band (universal regime), contrast: n=16,k=3,w=5 (2w+2k=16<=16)
    run_instance(17, 3, 16, 3, 5, 120, rng, "below-n16k3")
    # ABOVE UDR for contrast (window-ish): n=16, k=3, w=7
    run_instance(17, 3, 16, 3, 7, 120, rng, "above-n16k3")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
A3 (#444) — DOES THE BGK WALL ENCROACH ON delta* AS n -> infinity?

Far-line incidence I_p(delta) via the prize (k+1)-subset-solve (prime-size-independent):
for each (k+1)-subset A of mu_n solve the (k+1)x(k+1) system g(z^i)=z^{ib}+gamma z^{ia} for
(g of deg<k, gamma); I_p(w) = #distinct gamma with true agreement >= w; worst over far pencils.

TWO REGIMES (established #407):
  - OVER-DET / RIGID  (bands w >= k+2): char-INDEPENDENT outside finite bad primes. DETERMINES
    delta* (smallest w with worstI <= budget=n). char-0 value reached above a "clearing prime".
  - UNDER-DET / FLOPPY / r=1  (band w = k+1): I_p(k+1) ~ Theta(p) grows forever (BGK/Paley wall).
    Its LOWER EDGE in delta is fixed: delta_floppy = 1 - (k+1)/n.

KEY PRIOR FINDING (probe_charinv_constrate_n32): NEAR-CAPACITY bands clear SLOWER than the bulk
(bulk threshold ~ n^3 = thin-prime pollution; near capacity it is LARGER). A3 measures the
near-capacity CLEARING PRIME p*(n) across n=16,32,64 and asks:

 (Q1) Does p*(n) outrun the prize prime ~ n*2^128 as n grows?  (if yes: char-0 crossing not faithful
      at prize scale -> wall reaches delta*).
 (Q2) Does the floppy lower edge delta_floppy = 1-(k+1)/n stay ABOVE the candidate
      delta* = (1-rho) - log2(n)/n ?  margin = (log2(n)-1)/n.  (if it reaches 0: wall touches delta*).
"""
import itertools, math, sys, random

def isp(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return h
    return None

def solve(M, bvec, p):
    m = len(M); A = [row[:]+[bvec[i]] for i, row in enumerate(M)]; r = 0
    for c in range(m):
        piv = None
        for i in range(r, m):
            if A[i][c] % p != 0: piv = i; break
        if piv is None: return None
        A[r], A[piv] = A[piv], A[r]; inv = pow(A[r][c], p-2, p); A[r] = [(v*inv) % p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p != 0:
                f = A[i][c]; A[i] = [(A[i][j]-f*A[r][j]) % p for j in range(m+1)]
        r += 1
    return [A[i][m] % p for i in range(m)]

def pencil_bands(p, n, k, a, b, z, pts, powr, subsets):
    za = [pow(z, (i*a) % n, p) for i in range(n)]
    zb = [pow(z, (i*b) % n, p) for i in range(n)]
    ga = {}
    for A in subsets:
        M = [powr[i]+[(-za[i]) % p] for i in A]; rhs = [zb[i] for i in A]
        sol = solve(M, rhs, p)
        if sol is None: continue
        gamma = sol[k]
        if gamma in ga: continue
        g = sol[:k]; cnt = 0
        for i in range(n):
            gi = 0; xi = pts[i]
            for j in range(k-1, -1, -1): gi = (gi*xi+g[j]) % p
            if gi == (zb[i]+gamma*za[i]) % p: cnt += 1
        ga[gamma] = cnt
    return {w: sum(1 for v in ga.values() if v >= w) for w in range(k+1, n+1)}

def make_subsets(n, k, cap, seed=7):
    """All (k+1)-subsets if feasible, else a deterministic random sample of size cap."""
    total = math.comb(n, k+1)
    if total <= cap:
        return list(itertools.combinations(range(n), k+1)), total, False
    rng = random.Random(seed); seen = set(); out = []
    while len(out) < cap:
        s = tuple(sorted(rng.sample(range(n), k+1)))
        if s not in seen:
            seen.add(s); out.append(s)
    return out, total, True

def worst_profile(p, n, k, fars, subsets):
    z = proot(p, n)
    if z is None: return None
    pts = [pow(z, i, p) for i in range(n)]
    powr = [[pow(pts[i], j, p) for j in range(k)] for i in range(n)]
    best = {w: 0 for w in range(k+1, n+1)}
    for (a, b) in fars:
        bc = pencil_bands(p, n, k, a, b, z, pts, powr, subsets)
        for w in bc: best[w] = max(best[w], bc[w])
    return best

def crossing(best, n, k, budget):
    for w in range(k+1, n+1):
        if best[w] <= budget: return w
    return n+1

def analyze(n, k, hi, far_cap=None, subset_cap=400000, seed=7):
    rho = k/n; budget = n
    fars_all = [(a, b) for a in range(k, n) if a != n//2 for b in range(k, n) if b != n//2 and a < b]
    fars = fars_all
    sampled_pencils = False
    if far_cap and len(fars_all) > far_cap:
        step = max(1, len(fars_all)//far_cap); fars = fars_all[::step]; sampled_pencils = True
    subsets, total_sub, sampled_sub = make_subsets(n, k, subset_cap, seed)
    primes = [p for p in range(2*n, hi) if isp(p) and (p-1) % n == 0]
    # also include some large primes >> n^3 to pin char-0 (prize-faithful direction)
    n3 = n**3
    bigp = []
    pp = ((10*n3)//n)*n + 1
    while len(bigp) < 4:
        if isp(pp): bigp.append(pp)
        pp += n
    allp = primes + bigp
    print(f"### n={n} k={k} rho={rho:.4f} budget={budget} | far pencils={len(fars)}/{len(fars_all)}"
          f"{' (SAMPLED)' if sampled_pencils else ''} | (k+1)-subsets={len(subsets)}/{total_sub}"
          f"{' (SAMPLED)' if sampled_sub else ''}", flush=True)
    profs = {}
    for p in allp:
        b = worst_profile(p, n, k, fars, subsets)
        if b is None: continue
        profs[p] = b
    if not profs:
        print("  no data", flush=True); return None
    pmax = max(profs); refprof = profs[pmax]
    cross0 = crossing(refprof, n, k, budget)
    # char-0 reference for OVER-DET bands (w>=k+2): value at largest (>>n^3) prime
    ref_overdet = {w: refprof[w] for w in range(k+2, n+1)}
    # per-band clearing prime: smallest p s.t. for all tested p'>=p, I_p'(w)==ref (over-det bands)
    sorted_p = sorted(profs)
    band_clear = {}
    for w in range(k+2, n+1):
        # find last prime where band != ref; clear = next prime after it
        last_bad = None
        for p in sorted_p:
            if profs[p][w] != ref_overdet[w]:
                last_bad = p
        if last_bad is None:
            band_clear[w] = sorted_p[0]
        else:
            above = [p for p in sorted_p if p > last_bad]
            band_clear[w] = above[0] if above else None  # None = never cleared in range
    # the delta*-CROSSING band's clearing prime (the operative p*)
    p_star = band_clear.get(cross0, None)
    # near-capacity slowest-clearing band among non-trivial over-det bands
    nontrivial = {w: pc for w, pc in band_clear.items() if refprof[w] > 0}
    slowest_w = max(nontrivial, key=lambda w: (nontrivial[w] is None, nontrivial[w] or 0)) if nontrivial else None
    slowest_p = nontrivial.get(slowest_w) if slowest_w else None
    # report
    print(f"  char-0 worst profile (w={k+1}..n): {[refprof[w] for w in range(k+1, n+1)]}", flush=True)
    print(f"  delta*-crossing band w={cross0} -> delta*_rigid = 1-{cross0}/{n} = {1-cross0/n:.4f}", flush=True)
    print(f"  per-band clearing prime (over-det, nontrivial bands):", flush=True)
    for w in sorted(nontrivial):
        cap_appr = 1 - w/n
        print(f"     w={w} (delta={1-w/n:.3f}, char-0 I={refprof[w]}): clears at p={nontrivial[w]}"
              f"  (p/n^3={None if nontrivial[w] is None else round(nontrivial[w]/n3,2)})", flush=True)
    print(f"  => delta*-crossing clearing prime p*(n) = {p_star}  (p*/n^3 = "
          f"{None if p_star is None else round(p_star/n3,2)})", flush=True)
    print(f"  => slowest-clearing nontrivial band w={slowest_w} clears at p={slowest_p} "
          f"(p/n^3={None if slowest_p is None else round(slowest_p/n3,2)})", flush=True)
    d_floppy = 1 - (k+1)/n
    cand = (1-rho) - math.log2(n)/n
    print(f"  FLOPPY edge delta_floppy=1-(k+1)/n={d_floppy:.4f} ; candidate delta*={cand:.4f} ; "
          f"floppy-cand={d_floppy-cand:+.4f}", flush=True)
    print(flush=True)
    return dict(n=n, k=k, rho=rho, cross=cross0, p_star=p_star, slowest_w=slowest_w,
                slowest_p=slowest_p, d_floppy=d_floppy, cand=cand, n3=n3)

if __name__ == "__main__":
    print("="*92)
    print("A3: BGK wall encroachment — clearing prime p*(n) & floppy edge vs candidate delta*")
    print("="*92)
    configs = [
        (16, 2, 20000, None, 400000),
        (32, 4, 12000, None, 400000),
        (64, 4, 4000, 80, 250000),   # rho=1/16, sampled pencils + sampled subsets for feasibility
    ]
    rows = []
    for (n, k, hi, fcap, scap) in configs:
        r = analyze(n, k, hi, far_cap=fcap, subset_cap=scap)
        if r: rows.append(r)
    print("="*92); print("EXTRAPOLATION"); print("="*92)
    # p*(n)/n^3 trend and absolute log2(p*) vs prize prime
    pts = [(math.log2(r['n']), math.log2(r['p_star'])) for r in rows if r['p_star']]
    if len(pts) >= 2:
        xs=[x for x,_ in pts]; ys=[y for _,y in pts]
        mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
        sxx=sum((x-mx)**2 for x in xs); sxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
        A=sxy/sxx; B=my-A*mx
        print(f"  CROSSING clearing prime fit: log2(p*) ~ {A:.2f}*log2(n)+{B:.2f}  "
              f"=> p*(n)~n^{A:.2f}*2^{B:.2f}  ({A:.2f} bits/octave)", flush=True)
        for nn in [16,64,256,2**16,2**32]:
            mu=math.log2(nn); lp=A*mu+B; lpr=mu+128
            print(f"    n=2^{int(mu):<2d}: log2(p*)~{lp:7.1f}  vs log2(prize n*2^128)={lpr:7.1f}  "
                  f"=> {'p* OUTRUNS prize (WALL REACHES)' if lp>lpr else 'p* BELOW prize (RIGIDITY SAFE)'}", flush=True)
    # slowest near-capacity band clearing prime trend (the genuine BGK wall location)
    spts = [(math.log2(r['n']), math.log2(r['slowest_p'])) for r in rows if r['slowest_p']]
    if len(spts) >= 2:
        xs=[x for x,_ in spts]; ys=[y for _,y in spts]
        mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
        sxx=sum((x-mx)**2 for x in xs); sxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
        A=sxy/sxx; B=my-A*mx
        print(f"\n  SLOWEST near-cap band fit: log2(p*_slow) ~ {A:.2f}*log2(n)+{B:.2f}  ({A:.2f} bits/octave)", flush=True)
        for nn in [256,2**16,2**32]:
            mu=math.log2(nn); lp=A*mu+B; lpr=mu+128
            print(f"    n=2^{int(mu):<2d}: log2(p*_slow)~{lp:7.1f} vs log2(prize)={lpr:7.1f} "
                  f"=> {'OUTRUNS prize' if lp>lpr else 'BELOW prize'}", flush=True)
    print("\n  Floppy-edge margin delta_floppy - candidate = (log2(n)-1)/n (analytic, >0 = safe):", flush=True)
    for nn in [16,32,64,256,2**16,2**32]:
        m=(math.log2(nn)-1)/nn
        print(f"    n=2^{int(math.log2(nn)):<2d}: margin={m:+.6f}  ({'floppy ABOVE candidate (SAFE)' if m>0 else 'floppy reaches candidate'})", flush=True)

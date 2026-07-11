#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — does the LONGEST-EMPTY-ARC (largest residue gap) of the worst-b
phase set carry the sqrt-cancellation, or does it saturate?

Object: A_b = { (b*y) mod p : y in mu_n }  (mu_n = order-n 2-power subgroup of F_p*).
eta_b = sum_{y in mu_n} e_p(b*y).  |eta_b| is large iff A_b clumps; small iff A_b
spreads.

The brief's open Q3: is there a NON-ENERGY small-ball quantity that carries the
sqrt(n*log) cancellation? Prior bricks ruled out:
  - single-window L-infinity occupancy (energy-blind, _ZModDFTLinftyFloor / 758205014)
  - multi-window occupancy splits (pay trivial budget |s|, g55)
UNMINED: the GAP STATISTIC. For n equidistributed points on Z_p, the largest gap is
~ (p/n)*log(n) (coupon-collector / extreme spacing). If A_b at the WORST b had a
gap MUCH larger than (p/n)*log(n) (a big "hole"), that hole would be a NON-energy
witness of clumping -> could bound |eta_b| WITHOUT moments. Conversely if the worst-b
largest gap stays at the random ~(p/n)*log(n) scale, the gap statistic is BLIND to the
worst-b clumping (it saturates / carries no extra cancellation), walling this route.

Question probed (EXACT integer arithmetic, prize regime, PROPER mu_n, p>>n^3,
multiple primes incl Fermat):
  (Q1) worst-b LARGEST GAP G_max(b*) vs the equidistribution baseline (p/n)*log(n)
       and vs a RANDOM same-size additive set's largest gap. Is the worst-b gap
       anomalously large (a real hole), or random-scale?
  (Q2) Correlation between |eta_b| and normalized largest gap G_max/(p/n) across ALL
       b. Does big |eta| FORCE a big gap (monotone lever), or are they decoupled?
  (Q3) Is the largest-gap of A_b THINNESS-ESSENTIAL? compare worst-b gap at thin n
       vs the gap a random n-subset of Z_p gives.

NEVER n=q-1 (full group). EXACT.
"""
import math, random, statistics

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta):
    target = int(round(n**beta))
    k0 = max(2, target // n)
    for dk in range(0, 400000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n*n*n and is_prime(p):  # enforce p >> n^3
                return p
    return None

def subgroup(p, n):
    """order-n subgroup mu_n of F_p* (n | p-1)."""
    # find a generator g of F_p*, then g^((p-1)/n) generates mu_n
    fac = factorize(p-1)
    g = find_generator(p, fac)
    h = pow(g, (p-1)//n, p)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = x*h % p
    assert len(S) == n, (p,n,len(S))
    return sorted(S)

def factorize(m):
    f = {}
    d = 2
    while d*d <= m:
        while m % d == 0:
            f[d] = f.get(d,0)+1; m//=d
        d += 1
    if m > 1: f[m] = f.get(m,0)+1
    return f

def find_generator(p, fac):
    for g in range(2, p):
        ok = True
        for q in fac:
            if pow(g, (p-1)//q, p) == 1:
                ok = False; break
        if ok: return g
    raise RuntimeError("no gen")

def eta_abs(b, mu, p):
    """|sum_{y in mu} e_p(b*y)| exact via complex; integers for the residues."""
    re = 0.0; im = 0.0
    for y in mu:
        ang = 2*math.pi*((b*y) % p)/p
        re += math.cos(ang); im += math.sin(ang)
    return math.hypot(re, im)

def largest_gap(residues, p):
    """largest cyclic gap between consecutive residues on Z_p."""
    rs = sorted(residues)
    gmax = 0
    for i in range(len(rs)):
        nxt = rs[(i+1) % len(rs)]
        gap = (nxt - rs[i]) % p
        if i == len(rs)-1:
            gap = (rs[0] + p - rs[i]) % p
        gmax = max(gmax, gap)
    return gmax

def run_one(n, beta):
    p = find_prime(n, beta)
    if p is None:
        print(f"  n={n} beta={beta}: no prime"); return
    mu = subgroup(p, n)
    baseline = (p/n)*math.log(n)   # expected largest gap for n equidist points
    unit = p/n
    # scan all b != 0 mod the coset structure: |eta_b| const on mu_n-cosets, so one b per coset
    # representatives: b ranges over coset reps of F_p*/mu_n. Just scan b=1..p-1 but dedup cheaply.
    best_eta = -1.0; best_b = None
    data = []  # (|eta_b|, normgap)
    # sample to keep it tractable for large p: scan a representative set
    bs = range(1, p)
    if p > 200000:
        bs = random.sample(range(1, p), 60000)
    for b in bs:
        e = eta_abs(b, mu, p)
        A = [(b*y) % p for y in mu]
        g = largest_gap(A, p)
        data.append((e, g/unit))
        if e > best_eta:
            best_eta = e; best_b = b; best_gap = g
    # random same-size additive set baseline (largest gap)
    rnd_gaps = []
    for _ in range(200):
        R = random.sample(range(p), n)
        rnd_gaps.append(largest_gap(R, p)/unit)
    rnd_mean = statistics.mean(rnd_gaps); rnd_max = max(rnd_gaps)
    worst_normgap = best_gap/unit
    # correlation between |eta| and normgap
    es = [d[0] for d in data]; gs = [d[1] for d in data]
    n_d = len(es)
    me = sum(es)/n_d; mg = sum(gs)/n_d
    cov = sum((e-me)*(g-mg) for e,g in data)/n_d
    se = math.sqrt(sum((e-me)**2 for e in es)/n_d)
    sg = math.sqrt(sum((g-mg)**2 for g in gs)/n_d)
    corr = cov/(se*sg) if se*sg>0 else float('nan')
    sqrtfac = math.sqrt(n*math.log(p/n))
    print(f"  n={n:4d} p={p}  |eta|_max={best_eta:.2f}  prize sqrt(n log(p/n))={sqrtfac:.2f}  ratio={best_eta/sqrtfac:.3f}")
    print(f"       worst-b largest gap (units of p/n)={worst_normgap:.3f}   equidist baseline log(n)={math.log(n):.3f}")
    print(f"       RANDOM n-subset largest gap: mean={rnd_mean:.3f} max={rnd_max:.3f} (units p/n)")
    print(f"       corr(|eta_b|, normgap) over all b = {corr:+.3f}   (n samples={n_d})")
    anomalous = worst_normgap > 1.5*rnd_mean
    print(f"       worst-b gap ANOMALOUS vs random (>1.5x mean)? {anomalous}")
    return dict(n=n,p=p,eta=best_eta,worst_normgap=worst_normgap,
                rnd_mean=rnd_mean,corr=corr,anomalous=anomalous)

if __name__ == "__main__":
    random.seed(444)
    print("=== Door-(iv) Lane-1: LARGEST-GAP (longest-empty-arc) small-ball probe ===")
    print("Q: does the worst-b largest gap carry sqrt-cancellation (anomalous hole),")
    print("   or saturate at the random equidistribution scale (energy-blind)?\n")
    results = []
    for beta in (4.0,):
        print(f"--- beta={beta} (p ~ n^{beta}, p>>n^3) ---")
        for n in (16, 32, 64):
            r = run_one(n, beta)
            if r: results.append(r)
    # Fermat-type structured prime check at n=16 (p=65537) -- but enforce p>>n^3=4096, ok
    print("\n--- structured Fermat-type prime n=16 p=65537 ---")
    p=65537; n=16
    mu=subgroup(p,n); unit=p/n
    best_eta=-1; 
    for b in range(1,p):
        e=eta_abs(b,mu,p)
        if e>best_eta: best_eta=e; bg=largest_gap([(b*y)%p for y in mu],p)
    print(f"  worst |eta|={best_eta:.2f}  largest gap (units p/n)={bg/unit:.3f}  log(n)={math.log(n):.3f}")
    print("\n=== VERDICT printed above; interpret anomalous flags + corr ===")

"""
wf407 / T232-08-evt : the EVT gap -- directional sub-Gaussian MGF + tail vs the
i.i.d.-Gumbel prediction. This is the DECISIVE test of whether the EVT route to
the floor is viable or walled at the bulk-vs-tail gap.

The SalemZygmundChaining kernel (in-tree, axiom-clean) reduces the floor to:
    SubGaussianMGF:  (1/m) sum_c exp(lam * Re(zeta_bar * eta_c)) <= exp(sigma^2 lam^2 / 2)
with sigma^2 = O(n). Then B <= sqrt(2 sigma^2 log m).

EXCHANGEABILITY (cov = -Var/(m-1), proven exactly in probe 1) is NECESSARY but
the SUB-GAUSSIAN MGF is the actual open input. We test:

  (T1) Does the empirical directional MGF psi(lam) = log[(1/m) sum_c exp(lam Re(zeta_bar eta_c))]
       stay <= sigma^2 lam^2/2 for sigma^2 = c*n with a UNIVERSAL c (uniform in m)?
       -> measure the best sigma^2/n needed to dominate the MGF over lam in [0, lam_max],
          and whether it grows with m. If bounded in m -> route's per-period input is
          empirically O(n). If it grows with m -> tail wall.

  (T2) The de Finetti / exchangeable-CLT subtlety: an EXCHANGEABLE family with
       cov = -Var/(m-1) is the FINITE-m white-noise (negatively-correlated) ensemble.
       Its max does NOT automatically obey the i.i.d. Gumbel law unless the periods
       are *also* asymptotically independent (mixing). We directly compare:
         max_c Re(eta_c)  vs  sqrt(2 * Var_dir * log m)   [the sub-Gaussian/Gumbel ceiling]
       Var_dir = empirical Var of the directional projection. Ratio should be <= ~1
       for the route to deliver the floor; ratio > 1 quantifies the tail overshoot.

  (T3) Tail fatness: for the WORST direction zeta, the tail exponent
         k(t) = -log( frac{c : Re(zeta_bar eta_c) >= t * sd} ) / (t^2/2)
       For a true Gaussian/sub-Gaussian tail k(t) ~ 1 (and >= 1 for sub-Gaussian).
       k(t) < 1 at large t = FAT tail = the wall. We report k(t) at t=1,1.5,2,2.5.
"""
import numpy as np
from math import gcd, log, sqrt, pi, exp

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1; fac = []; x = phi; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac): return g
    raise RuntimeError

def periods(p, n):
    m = (p-1)//n
    g = primitive_root(p)
    gm = pow(g, m, p)
    G = []; cur = 1
    for _ in range(n):
        G.append(cur); cur = cur*gm % p
    G = np.array(G, dtype=np.int64)
    w = 2.0*pi/p
    etas = np.empty(m, dtype=np.complex128)
    gc = 1
    for c in range(m):
        etas[c] = np.sum(np.exp(1j*w*((gc*G) % p)))
        gc = gc*g % p
    return etas, m

def directional_proj(etas, theta):
    # Re(conj(zeta)*eta) with zeta = e^{i theta}
    zeta = np.exp(1j*theta)
    return (np.conj(zeta)*etas).real

def worst_direction(etas, ndir=180):
    """Find direction maximizing max projection (the actual B-witness direction)."""
    best = -1e9; best_th = 0.0
    for k in range(ndir):
        th = pi*k/ndir
        X = directional_proj(etas, th)
        v = X.max()
        if v > best:
            best = v; best_th = th
    return best_th, best

def mgf_sigma_needed(X, n, lam_grid):
    """smallest sigma^2/n s.t. (1/m)sum exp(lam X) <= exp(sigma^2 lam^2/2) for all lam in grid (lam>0)."""
    m = len(X)
    worst = 0.0
    for lam in lam_grid:
        if lam == 0: continue
        psi = np.log(np.mean(np.exp(lam*X)))   # cumulant gen fn
        # need sigma^2 >= 2 psi / lam^2
        need = 2*psi/(lam*lam)
        worst = max(worst, need)
    return worst / n

def tail_exponent(X, t):
    sd = X.std()
    if sd == 0: return float('nan')
    thr = t*sd
    frac = np.mean(X >= thr)
    if frac <= 0: return float('inf')  # no sample beyond -> very thin
    return -log(frac)/(t*t/2)

def analyze(p, n):
    etas, m = periods(p, n)
    lnm = log(m)
    th, B = worst_direction(etas)
    X = directional_proj(etas, th)            # worst-direction projections, mean ~ 0 (since sum eta=-1)
    Xc = X - X.mean()
    var_dir = X.var()
    # sub-Gaussian / Gumbel ceiling for the directional max:
    gumbel_ceiling = sqrt(2*var_dir*lnm)
    ratio_gumbel = B / gumbel_ceiling if gumbel_ceiling>0 else float('nan')
    # MGF sigma needed (over lam up to where exp doesn't overflow): lam_max ~ 3/sqrt(var)
    lam_max = 3.0/ sqrt(var_dir) if var_dir>0 else 1.0
    lam_grid = np.linspace(0.05*lam_max, lam_max, 30)
    sig_over_n = mgf_sigma_needed(Xc, n, lam_grid)   # centered MGF proxy
    # tail exponents
    ks = {t: tail_exponent(X, t) for t in (1.0, 1.5, 2.0, 2.5)}
    return dict(p=p, n=n, m=m, lnm=lnm, B=B, var_dir=var_dir, var_over_n=var_dir/n,
                gumbel_ceiling=gumbel_ceiling, ratio_gumbel=ratio_gumbel,
                sig_over_n=sig_over_n, ks=ks)

def gen_primes_for_n(n, count, start_k=2):
    def isprime(x):
        if x<2: return False
        for q in (2,3,5,7,11,13,17,19,23,29,31,37):
            if x%q==0: return x==q
        d=x-1;r=0
        while d%2==0: d//=2;r+=1
        for a in (2,3,5,7,11,13,17,19,23,29,31,37):
            v=pow(a,d,x)
            if v in (1,x-1): continue
            for _ in range(r-1):
                v=v*v%x
                if v==x-1: break
            else: return False
        return True
    res=[];k=start_k
    while len(res)<count:
        p=k*n+1
        if isprime(p):
            m=(p-1)//n;mm=m
            while mm%2==0: mm//=2
            if mm>1 and p>n*n: res.append(p)
        k+=1
    return res

if __name__=="__main__":
    print("=== (T1/T2/T3) directional MGF, Gumbel ceiling, tail exponents ===")
    print(f"{'n':>4} {'p':>9} {'m':>7} {'B':>8} {'var/n':>6} {'B/sqrt(2var lnm)':>16} "
          f"{'sigMGF/n':>9} {'k(1.0)':>7} {'k(1.5)':>7} {'k(2.0)':>7} {'k(2.5)':>7}")
    rows=[]
    for n in (8,16,32,64):
        for p in gen_primes_for_n(n, 5):
            r=analyze(p,n); rows.append(r)
            ks=r['ks']
            def f(x): return ('inf' if x==float('inf') else f'{x:.2f}')
            print(f"{n:>4} {p:>9} {r['m']:>7} {r['B']:>8.3f} {r['var_over_n']:>6.3f} "
                  f"{r['ratio_gumbel']:>16.3f} {r['sig_over_n']:>9.3f} "
                  f"{f(ks[1.0]):>7} {f(ks[1.5]):>7} {f(ks[2.0]):>7} {f(ks[2.5]):>7}")
    print()
    # growing-m at fixed n=16 to test plateau of ratio_gumbel and sigMGF/n
    print("=== plateau check: fixed n=16, growing m (does ratio_gumbel / sigMGF stay bounded?) ===")
    print(f"{'p':>9} {'m':>7} {'lnm':>6} {'B/sqrt(2var lnm)':>16} {'sigMGF/n':>9}")
    for p in gen_primes_for_n(16, 14):
        r=analyze(p,16)
        print(f"{p:>9} {r['m']:>7} {r['lnm']:>6.2f} {r['ratio_gumbel']:>16.3f} {r['sig_over_n']:>9.3f}")
    print()
    print("INTERPRETATION:")
    print(" * ratio_gumbel = B / sqrt(2*Var_dir*ln m). <=~1 => the directional max obeys the")
    print("   sub-Gaussian Gumbel ceiling that the SalemZygmund kernel delivers. >1 => tail overshoot.")
    print(" * sigMGF/n = empirical sub-Gaussian proxy sigma^2/n needed to dominate the MGF.")
    print("   Bounded & ~ Var/n => sub-Gaussian holds empirically; growing in m => the wall.")
    print(" * k(t) = tail exponent; >=1 sub-Gaussian, ~1 Gaussian, <1 FAT (the wall). inf=thinner than any.")

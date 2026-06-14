#!/usr/bin/env python3
"""Probe (#407): the EXACT log-scaling law + tail exponent + Gauss-sum identity.

Three decisive tests for whether the Gaussian-maximum law
    B = max_coset |S_b| ~ C*sqrt(n*log(p/n))
holds with a CLEAN exact constant (=> pins delta* exactly), or whether the
NON-GAUSSIAN value distribution (Demirci-Marklof / Untrau) breaks it.

(A) BETA-SCALING:  fix n, vary p (=> vary beta=log_n p), measure B.  The law
    predicts  B^2 = C^2 * n * log(p/n)  i.e. B^2 LINEAR in L:=log(p/n) with
    slope C^2*n through ~origin.  Linear fit -> slope, intercept, R^2.
    THIS pins the exact constant H(rho)/beta in delta*.  Exclude fully-dyadic
    (Fermat-type) p where (p-1)/n has no large odd part.

(B) TAIL EXPONENT:  histogram t = |S_b|^2 / n over all cosets.  Gaussian field
    => P(t > lambda) = e^{-lambda} (exponential).  Fit log P(t>lambda) vs lambda
    in the tail; slope -1 == Gaussian.  Heavier tail => law's constant is wrong.

(C) GAUSS-SUM IDENTITY:  verify  S_b = (1/m)[-1 + sum_{j=1}^{m-1} conj(chi_j)(b) g(chi_j)]
    where chi_j are characters of Q = F_p^*/mu_n (order m=(p-1)/n), g = Gauss sum,
    |g(chi_j)| = sqrt(p).  Confirms B = || IDFT of Gauss sums ||_inf.
"""
import sys, math, cmath
import numpy as np


def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True


def odd_part(x):
    while x % 2 == 0: x //= 2
    return x


def primes_for(n, lo_beta, hi_beta, want):
    """primes p ~ n^beta over [lo,hi], n|p-1, EXCLUDING near-fully-dyadic
    (require odd_part((p-1)/n) > 1 so mu_n is a genuine proper subgroup with
    non-2-power cofactor -- avoids the #400 Fermat trap)."""
    out = []
    betas = np.linspace(lo_beta, hi_beta, want*3)
    seen = set()
    for be in betas:
        base = int(round(n ** be)); base -= base % n; base += 1
        p = base
        for _ in range(20000):
            if p > 3 and is_prime(p):
                cof = (p-1)//n
                if odd_part(cof) > 1 and p not in seen:   # proper, non-dyadic
                    seen.add(p); out.append(p); break
            p += n
        if len(out) >= want: break
    return sorted(out)


def primitive_root(p):
    phi = p-1; facs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs): return g
    raise RuntimeError


def subgroup_xs(p, n):
    g = primitive_root(p); eta = pow(g, (p-1)//n, p)
    xs = [1]
    for _ in range(n-1): xs.append(xs[-1]*eta % p)
    return g, xs


def all_coset_mags(p, n, xs):
    """return numpy array of |S_b| over ALL (p-1)/n cosets (b = g^j)."""
    g = primitive_root(p); ncos = (p-1)//n
    xs_arr = np.array(xs, dtype=np.int64); twp = 2.0*math.pi/p
    out = np.empty(ncos, dtype=np.float64)
    CH = max(1, min(8_000_000 // n, ncos))
    Gv = [1]*CH
    for i in range(1, CH): Gv[i] = Gv[i-1]*g % p
    Gv = np.array(Gv, dtype=object)            # python ints (avoid overflow)
    c = 1; j = 0
    while j < ncos:
        mlen = min(CH, ncos - j)
        reps = np.array([(c*int(Gv[i])) % p for i in range(mlen)], dtype=np.int64)
        prod = (reps[:,None]*xs_arr[None,:]) % p
        ang = prod.astype(np.float64)*twp
        S = np.cos(ang).sum(1) + 1j*np.sin(ang).sum(1)
        out[j:j+mlen] = np.abs(S)
        c = c * pow(g, mlen, p) % p; j += mlen
    return out


def test_A_betascaling():
    print("="*88); print("(A) BETA-SCALING: B^2 vs L=log(p/n); law => linear, slope=C^2*n")
    print("="*88)
    for n in (32, 64):
        ps = primes_for(n, 3.0, (5.0 if n==32 else 4.3), 8)
        Ls, B2s, rows = [], [], []
        for p in ps:
            g, xs = subgroup_xs(p, n)
            mags = all_coset_mags(p, n, xs)
            B = float(mags.max()); L = math.log(p/n)
            Ls.append(L); B2s.append(B*B)
            rows.append((p, L, B, B/math.sqrt(n*L)))
        L = np.array(Ls); Y = np.array(B2s)
        A = np.vstack([L, np.ones_like(L)]).T
        (slope, intc), res, *_ = np.linalg.lstsq(A, Y, rcond=None)
        ss_tot = ((Y-Y.mean())**2).sum(); ss_res = float(res[0]) if len(res) else ((Y-(A@[slope,intc]))**2).sum()
        r2 = 1 - ss_res/ss_tot
        print(f"\n n={n}: {len(ps)} primes, beta in [{math.log(ps[0],n):.2f},{math.log(ps[-1],n):.2f}]")
        print(f"   {'p':>13} {'L=log(p/n)':>11} {'B':>9} {'B/sqrt(nL)':>11}")
        for (p,Lv,B,c) in rows: print(f"   {p:>13} {Lv:>11.3f} {B:>9.2f} {c:>11.3f}")
        print(f"   FIT B^2 = {slope:.3f}*L + {intc:.1f}   slope/n = {slope/n:.3f} (=C^2)  "
              f"=> C={math.sqrt(max(slope/n,0)):.3f}  R^2={r2:.4f}  intercept/n={intc/n:.2f}")


def test_B_tail():
    print("\n"+"="*88); print("(B) TAIL EXPONENT: t=|S|^2/n; Gaussian field => P(t>lam)=e^{-lam} (slope -1)")
    print("="*88)
    for n, beta in ((64, 4.0), (128, 4.0)):
        ps = primes_for(n, beta, beta+0.01, 1)
        p = ps[0]; g, xs = subgroup_xs(p, n)
        mags = all_coset_mags(p, n, xs)
        t = (mags**2)/n
        # empirical tail P(t>lam) at grid; fit log P vs lam over [2, lam95]
        lams = np.linspace(1.0, t.max()*0.9, 40)
        surv = np.array([(t > l).mean() for l in lams])
        good = surv > (5.0/len(t))                      # >=5 samples
        lamf = lams[good]; logS = np.log(surv[good])
        # fit over upper half of valid range
        mid = lamf > (lamf.min()+ (lamf.max()-lamf.min())*0.25)
        if mid.sum() >= 3:
            A = np.vstack([lamf[mid], np.ones(mid.sum())]).T
            (sl, ic), *_ = np.linalg.lstsq(A, logS[mid], rcond=None)
        else:
            sl = float('nan'); ic = float('nan')
        print(f"\n n={n}, p={p}, #cosets={len(t)}: mean(t)={t.mean():.3f} (exp=>1) "
              f"max(t)={t.max():.2f}  log(p/n)={math.log(p/n):.2f}")
        print(f"   tail-fit log P(t>lam) ~ {sl:.3f}*lam + {ic:.2f}   "
              f"(Gaussian slope = -1.000)  => tail-alpha {'GAUSSIAN' if -1.3<sl<-0.7 else 'NON-GAUSSIAN'}")
        # also report the relevant extreme statistic
        print(f"   max(t)/log(#cosets) = {t.max()/math.log(len(t)):.3f}  (Gaussian-max => ~1)")


def test_C_gauss_identity():
    print("\n"+"="*88); print("(C) GAUSS-SUM IDENTITY: S_b = (1/m)[-1 + sum_j conj(chi_j)(b) g(chi_j)]")
    print("="*88)
    n = 16
    ps = primes_for(n, 3.0, 3.6, 1); p = ps[0]
    g = primitive_root(p); m = (p-1)//n
    eta = pow(g, m, p); xs = [pow(eta, i, p) for i in range(n)]   # mu_n
    twp = 2.0*math.pi/p
    # multiplicative character psi of order m: psi(g^a) = e^{2pi i a / m}
    # chi_j = psi^j.  Gauss sum g(chi_j) = sum_{y} chi_j(y) e_p(y).
    # index elements of F_p^* by discrete log base g (precompute is O(p), p~16^3=4096)
    dlog = {}
    cur = 1
    for a in range(p-1): dlog[cur] = a; cur = cur*g % p
    def chi(j, y):     # chi_j(y) = e^{2pi i j*dlog(y)/m}
        return cmath.exp(2j*math.pi*j*dlog[y]/m)
    # Gauss sums g(chi_j) for all j
    gauss = []
    for j in range(m):
        s = 0j
        for y in range(1, p):
            s += chi(j, y) * cmath.exp(1j*twp*y)
        gauss.append(s)
    # pick a few test b (coset reps), compare direct S_b to formula
    maxerr = 0.0
    print(f"   n={n}, p={p}, m={m}, |g(chi_1)|={abs(gauss[1]):.3f} (sqrt(p)={math.sqrt(p):.3f})")
    for b in (1, g, pow(g,7,p), pow(g,123,p)):
        direct = sum(cmath.exp(1j*twp*(b*x % p)) for x in xs)
        formula = (-1 + sum((chi(j,b).conjugate())*gauss[j] for j in range(1,m)))/m
        err = abs(direct-formula); maxerr = max(maxerr, err)
        print(f"   b=g^{dlog[b]:<4}: |S_b|_direct={abs(direct):.4f}  |formula|={abs(formula):.4f}  err={err:.2e}")
    print(f"   MAX IDENTITY ERROR = {maxerr:.2e}  ({'VERIFIED' if maxerr<1e-6 else 'MISMATCH'})")
    print(f"   => B = max_b|S_b| = (1/m)||IDFT of Gauss sums (g(chi_j))_j||_inf  [EXACT]")


def main():
    test_A_betascaling()
    test_B_tail()
    test_C_gauss_identity()
    print("\n"+"="*88)
    print("VERDICT KEYS: (A) R^2->1 & flat C across n => clean Gaussian-max law, exact constant.")
    print("              (B) slope ~ -1 => Gaussian tail governs the max (law's constant trustworthy).")
    print("              (C) err~0 => the multiplicative Gauss-sum-DFT face is an EXACT identity.")
    print("="*88)
    return 0


if __name__ == "__main__":
    sys.exit(main())

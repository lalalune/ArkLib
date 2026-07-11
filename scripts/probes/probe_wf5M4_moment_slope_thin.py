#!/usr/bin/env python3
"""
probe_wf5M4_moment_slope_thin.py  (#444, lane wf-M4)

REFINED prescreen of the NP / char-p moment sufficient lemma, in the THIN (prize) regime.

Part A of probe_wf5M4_newton_polygon.py found:  the real period moment
   W_r = (1/p) sum_b eta_b^r   (= #{ (x_i) in mu_n^r : sum x_i = 0 mod p })
satisfies  W_r / [ (r-1)!! * n^{r/2} ]  =:  rho_r(n,p)  and rho_r is NOT absolutely bounded over
ALL (n,p): at beta=1.52 it hits 51.8 (r=8).  BUT it decays toward 1 as beta grows.  The prize lives
at beta ~ 4-5.  THIS PROBE measures rho_r DEEP into thin beta and asks the decisive question:

  (Q-M4)  Is there an ABSOLUTE C and a depth law r(p) ~ ln p such that, for ALL n=2^mu and primes
          p = n^beta with beta >= beta0,   W_r <= C^r (r-1)!! n^{r/2}  for r <= ln p ?

If YES with C absolute (beta0 fixed), the moment-to-sup step gives M <= C' sqrt(n log(p/n)) -- prize.
The Newton-polygon CONTENT is the explanation of WHY rho_r -> 1 as beta grows:  the spurious mod-p
coincidences (tuples summing to 0 mod p but NOT a genuine antipodal/Lam-Leung matching) require
sum_i x_i = 0 mod p with the x_i NOT pairing antipodally; the number of such "non-matching" solutions
is ~ n^r / p (random model) which is << (r-1)!! n^{r/2} exactly when n^{r/2} << p / (r-1)!!, i.e.
   r/2 * log n  <  log p - log((r-1)!!)   <=>   r < 2 beta - (2/log n) log((r-1)!!).
This is the NP boundary in disguise:  the slope-0 (genuine-matching) part has count (r-1)!! n^{r/2};
the positive-slope (spurious, valuation >= 1 over Z but 0 mod p) part has count ~ n^r/p, subdominant
for r < 2 beta-ish.  THE SUFFICIENT LEMMA the prize reduces to:

   (SL-M4')   W_r  =  (genuine matchings) + (spurious)   with
              genuine  =  rho_r^Z (r-1)!! n^{r/2}    [rho_r^Z -> 1, char-0, Lam-Leung]
              spurious <=  n^r / p  *  Csp           [the off-diagonal sum-count, Csp absolute]
              ==>  W_r <= (r-1)!! n^{r/2} (1 + o(1))  for r <= 2 beta - eps  <=>  n^{r/2} <= p^{1-eps}.

The PRIZE depth is r ~ 2 log m / log n? -- we need r ~ ln p to optimize the sup; this lemma supports
r up to ~ 2 beta = 2 log p / log n, i.e. n^{r/2} up to p.  Optimizing sup at r=2beta gives
M <= ((2beta-1)!! n^beta)^{1/2beta} = sqrt(n) * ((2beta-1)!!)^{1/2beta} ~ sqrt(n) sqrt(2beta/e) ~
sqrt(n) sqrt(2 log(p/n)/(e log n)*... ).  Measure the actual achievable depth and the implied C.
"""
import math
import numpy as np

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def factor_small(m):
    f = {}; d = 2
    while d*d <= m:
        while m % d == 0: f[d] = f.get(d,0)+1; m //= d
        d += 1
    if m > 1: f[m] = f.get(m,0)+1
    return f

def primitive_root(p):
    fac = list(factor_small(p-1).keys())
    for g in range(2, p):
        if all(pow(g,(p-1)//q,p) != 1 for q in fac): return g
    return None

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    S = [pow(h, k, p) for k in range(n)]
    assert len(set(S)) == n
    return S

def eta(p, n):
    f = np.zeros(p)
    for x in subgroup(p, n): f[x] += 1.0
    return np.fft.fft(f).real

def dfac(k):           # (k-1)!!
    res = 1; j = k-1
    while j > 0: res *= j; j -= 2
    return res

def find_thin_primes(n, betas, count_each=2):
    """find primes p = n^beta-ish (within band) with n | p-1, p prime."""
    out = {}
    for beta in betas:
        target = n ** beta
        found = []
        # scan p = 1 + k*n around target
        k0 = max(1, int(target // n))
        for dk in range(0, 200000):
            for kk in (k0+dk, k0-dk):
                if kk < 1: continue
                p = 1 + kk*n
                if p > 4*target or p < target/4: continue
                if p > 6_000_000: continue
                if is_prime(p):
                    b = math.log(p)/math.log(n)
                    if abs(b-beta) < 0.25:
                        found.append((p, b))
            if len(found) >= count_each: break
        out[beta] = found[:count_each]
    return out

def run():
    print("="*92)
    print("wf-M4  THIN-regime moment-ratio prescreen of SL-M4'  (rho_r = W_r / ((r-1)!! n^{r/2}))")
    print("="*92)

    for n in [16, 32, 64]:
        print(f"\n##### n = {n}  (sqrt(n)={math.sqrt(n):.3f}) #####")
        pr = find_thin_primes(n, [2.0, 2.5, 3.0, 3.5, 4.0], count_each=1)
        for beta, lst in pr.items():
            for (p, b) in lst:
                ev = eta(p, n)
                rmax = min(2*int(b)+2, 12)
                rmax += rmax % 2          # even
                # predicted max useful depth r* = floor(2*beta) (n^{r/2} <= p)
                rstar = int(2*b)
                M = float(np.max(np.abs(ev[1:])))
                tgt = math.sqrt(n*math.log(p/n))
                print(f"  p={p:9d} beta={b:.2f}  m={(p-1)//n}  r*=floor(2beta)={rstar}  "
                      f"M={M:.3f} M/sqrt(nlog(p/n))={M/tgt:.3f}")
                line = "    rho_r:"
                worst = 0.0
                for r in range(2, rmax+1, 2):
                    Wr = float(np.sum(ev.astype(np.float64)**r)/p)
                    rho = Wr / (dfac(r)*n**(r/2))
                    inband = "*" if r <= rstar else " "
                    line += f"  r{r}{inband}={rho:6.3f}"
                    if r <= rstar: worst = max(worst, rho)
                print(line)
                print(f"    -> worst in-band (r<=r*) rho = {worst:.3f}   "
                      f"[SL-M4' wants this O(1), uniformly]")

    # the decisive C-extraction: across many thin primes, the implied moment constant
    print("\n##### Implied moment constant C from  W_r <= C^r (r-1)!! n^{r/2}  at r=r*=floor(2beta) #####")
    print("  (C = (rho_{r*})^{1/r*}; SL-M4' needs C bounded uniformly in n as beta fixed)")
    for n in [16, 32, 64]:
        row = f"  n={n:4d}: "
        for beta in [2.0, 2.5, 3.0, 3.5, 4.0]:
            pr = find_thin_primes(n, [beta], count_each=1)
            lst = pr[beta]
            if not lst:
                row += f" b{beta}:--- "; continue
            p, b = lst[0]
            ev = eta(p, n)
            rstar = max(2, int(2*b))
            rstar += rstar % 2
            Wr = float(np.sum(ev.astype(np.float64)**rstar)/p)
            rho = Wr/(dfac(rstar)*n**(rstar/2))
            C = rho**(1.0/rstar) if rho > 0 else 0
            row += f" b{b:.1f}:C={C:.2f}"
        print(row)

if __name__ == "__main__":
    run()

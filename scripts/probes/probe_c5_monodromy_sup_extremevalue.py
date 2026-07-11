#!/usr/bin/env python3
"""
ANGLE C5 (monodromy / Katz / Larsen) — the SUP-vs-AVERAGE tail question for
M(n) = max_{b != 0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x), mu_n = 2-power subgroup.

The C5 claim: Katz big-monodromy + Larsen's alternative => EFFECTIVE equidistribution of
{eta_b} to the limiting (vertical Sato-Tate, here complex-Gaussian) law, with explicit error.
Then an extreme-value / large-deviation argument bounds the MAX (the tail), giving
M(n) <= sqrt(2 n ln(p/n)) (the extreme of a Gaussian of variance n over ~p/n frequencies).

DISTINCTIVE TEST (NOT done by prior moment probes): the moment method already controls the
sup via the union bound, but pays the Wick constant (2r-1)!!^{1/r}. The monodromy+extreme-value
route would give a STRICTLY SHARPER sup IFF the actual TOP-TAIL of {|eta_b|/sqrt(n)} is genuinely
Gaussian (P(|eta|/sqrt(n) > t) ~ exp(-t^2)), so that the max over N=p/n frequencies is
~ sqrt(ln N) = sqrt(ln(p/n)), the extreme-value scaling.

If the top-tail is HEAVIER than Gaussian (the structured mod-p anomaly piling mass at the top),
the extreme-value argument FAILS and monodromy gives no gain beyond the moment method.

We test three things at PROPER mu_n (n = 2^mu, n | p-1, p PRIME, p >> n^3, NEVER n=p-1):
  (T1) bulk equidistribution: does the normalized {Re eta_b / sqrt(n/2)} match N(0,1)?
       (Sato-Tate / monodromy prediction for the BULK).
  (T2) the SUP scaling: is M(n)/sqrt(n) ~ sqrt(2 ln(p/n))? (extreme-value of Gaussian).
       Compare to (a) the trivial sqrt(2 ln N) Gaussian extreme, (b) the actual measured max.
  (T3) the TOP-TAIL exponent: fit P(|eta|/sqrt(n) > t) for t in the upper tail; Gaussian => exp(-t^2);
       extract the effective tail exponent alpha in exp(-c t^alpha). alpha >= 2 => extreme-value works;
       alpha < 2 (heavy tail) => monodromy/EVT route blocked.
"""
import math, cmath

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    for q in (3,5,7,11,13,17,19,23,29,31,37,41,43):
        if m % q == 0: return m == q
    d = m-1; s=0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % m == 0: continue
        x = pow(a,d,m); ok=(x==1)
        for _ in range(s):
            if x == m-1: ok=True; break
            x = x*x % m
        if not ok: return False
    return True

def find_prime(n, target):
    """smallest prime p >= target with n | p-1 (proper mu_n)."""
    p = target - (target % n) + 1
    for d in range(0, 400*n, n):
        if is_prime(p+d): return p+d
    return None

def subgroup_gen(p, n):
    for g0 in range(2, 500):
        g = pow(g0, (p-1)//n, p)
        if len({pow(g, i, p) for i in range(n)}) == n:
            return g
    return None

def all_periods(p, n):
    """Returns list of complex eta_b for b in 1..p-1 (b != 0). |list| = p-1."""
    g = subgroup_gen(p, n)
    H = [pow(g, i, p) for i in range(n)]
    tp = 2*math.pi/p
    etas = []
    for b in range(1, p):
        s = 0.0+0.0j
        for x in H:
            ang = tp * ((b*x) % p)
            s += cmath.exp(1j*ang)
        etas.append(s)
    return etas

print("="*100)
print("ANGLE C5 — monodromy/Larsen: does effective equidistribution control the SUP (tail)?")
print("="*100)
print("proper mu_n: n=2^mu, n|p-1, p PRIME, p>=n^beta. The MAX is the prize object.")
print()

# We can afford p up to ~ a few x 10^6 with (p-1) eta-evaluations each O(n).
cases = [(8,4),(8,5),(16,4),(16,5),(32,4),(8,6),(16,6)]
hdr = (f"{'n':>4} {'p':>10} {'beta':>5} {'N=p/n':>10} {'M/sqrtn':>9} "
       f"{'sqrt(2lnN)':>11} {'M/[sqn*sq2lnN]':>16} {'avg|eta|/sqn':>14} {'sqWick=sqpi/2':>14}")
print(hdr)
results = []
for (n, beta) in cases:
    p = find_prime(n, int(round(n**beta)))
    if not p or p > 25_000_000:
        print(f"{n:>4} {'(skip)':>10}")
        continue
    etas = all_periods(p, n)
    mags = [abs(e) for e in etas]
    M = max(mags)
    sqn = math.sqrt(n)
    N = (p-1)/n
    sq2lnN = math.sqrt(2*math.log(N))
    avg = sum(mags)/len(mags)
    # Gaussian-of-variance-n prediction for E|eta| = sqrt(n)*sqrt(pi/2)/sqrt(2)? 
    # Re,Im ~ N(0, n/2) each, |eta| ~ Rayleigh with E = sqrt(n*pi/4). E|eta|/sqrt(n)=sqrt(pi/4)=0.886
    rayl = math.sqrt(math.pi/4)
    ratio = M/(sqn*sq2lnN)
    print(f"{n:>4} {p:>10} {beta:>5} {N:>10.0f} {M/sqn:>9.3f} {sq2lnN:>11.3f} "
          f"{ratio:>16.3f} {avg/sqn:>14.3f} {rayl:>14.3f}")
    results.append((n,p,beta,etas,mags,M,sqn,N))
print()
print(">>> M/[sqrt(n)*sqrt(2 ln N)] near 1 (and stable) => SUP tracks GAUSSIAN extreme-value =>")
print(">>> monodromy+EVT route would deliver the prize sqrt(2n ln(p/n)). >1 and GROWING => heavy tail.")
print()

print("="*100)
print("T3 — the TOP-TAIL exponent: P(|eta|/sqrt(n) > t) vs Gaussian exp(-t^2)")
print("="*100)
print("Rayleigh tail (|eta|, Re/Im iid N(0,n/2)): P(|eta|/sqrt(n) > t) = exp(-t^2). Fit alpha in exp(-c t^alpha).")
print()
for (n,p,beta,etas,mags,M,sqn,N) in results:
    norm = sorted(m/sqn for m in mags)  # |eta|/sqrt(n), ascending
    total = len(norm)
    # upper-tail survival fn at a few thresholds; fit log(-log S) = log c + alpha log t
    ts = []; ys = []
    for t in [1.0, 1.3, 1.6, 1.9, 2.2, 2.5]:
        cnt = sum(1 for v in norm if v > t)
        if cnt >= 3 and cnt < total:
            S = cnt/total
            ts.append(math.log(t)); ys.append(math.log(-math.log(S)))
    if len(ts) >= 2:
        nfit = len(ts); sx=sum(ts); sy=sum(ys); sxx=sum(a*a for a in ts); sxy=sum(a*b for a,b in zip(ts,ys))
        alpha = (nfit*sxy - sx*sy)/(nfit*sxx - sx*sx)
        Smax = sum(1 for v in norm if v > M/sqn - 1e-9)/total
        print(f"  n={n:>3} p={p:>9} N={N:>9.0f}: tail exponent alpha = {alpha:>5.2f} "
              f"(Gaussian=2.0; <2 heavy, >2 light); top |eta|/sqn = {M/sqn:.3f}")
    else:
        print(f"  n={n:>3} p={p:>9}: too few tail points")
print()
print(">>> alpha >= 2 (Gaussian/light tail) at the TOP => EVT extreme-value argument is sound, the")
print(">>> max is sqrt(2 ln N)-controlled. alpha < 2 (heavy) => structured anomaly piles top mass =>")
print(">>> monodromy controls the BULK but NOT the sup => no gain over the moment/union-bound route.")

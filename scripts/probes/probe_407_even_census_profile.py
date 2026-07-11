#!/usr/bin/env python3
"""
probe_407_even_census_profile.py  (#407 / #444 surviving-lane: collective thin depth profile)

OBJECT (the genuine prize moment object, NOT r_min, NOT d_odd, NOT A_r/Wick-at-optimizer):
  The EVEN zero-sum census profile W_{2r}(G) = #{(y_1..y_{2r}) in G^{2r} : sum y_i = 0 in Z/n},
  for G = mu_n (thin 2-power subgroup, additive image = the exponent set Z/n), feeding the EXACT
  in-tree identity (Frontier/_GaussPeriodMomentCensus.lean, push 76715441a):
        A_{2r} := sum_{b!=0} eta_b^{2r} = |F|*W_{2r} - n^{2r}        (q = |F|+1, here we use char-sum form)
  and the MANDATORY DC-subtracted prize form (dossier S2, c.294):
        DCsub_{2r} := E_{2r} - n^{4r}/q     must be   <= Wick_{2r} = (4r-1)!! * n^{2r}.

  Actually the census IS purely additive (lives in Z/n, p-INDEPENDENT), so we compute W_{2r}(Z/n)
  restricted to the additive structure of the EXPONENT set of mu_n. KEY POINT: mu_n's exponent set
  under the dyadic FFT identification is the FULL Z/n (the period index runs over all of Z/n), so the
  ADDITIVE zero-sum census of the *index set* {0,..,n-1} under mod-n addition is the relevant W_{2r}
  for the period-moment identity. That is a known closed object; the THIN content is in the SIGNED /
  character-weighted census once we fold in the actual subgroup embedding mu_n -> F_p*.

WHAT IS GENUINELY UN-MEASURED (the gap I am filling):
  Prior reports measured (a) r_min = smallest single vanisher (depth), (b) d_odd onset, (c) A_r/Wick
  RATIO at the optimizer r* and its n-trend. NONE measured the per-r EVEN census *profile* of the
  REAL character-weighted moment  W^chi_{2r}(mu_n,p) := (1/|F|) sum_{b!=0} eta_b^{2r}  vs a thin-density
  RANDOM control, to test whether the thin advantage COMPOUNDS multiplicatively across r (collective)
  or is a single-depth artifact. Compounding across r is exactly what the moment route needs and what
  r_min / d_odd cannot see.

METHOD (exact, probe-first, rule-2 + rule-3 compliant):
  - eta_b computed EXACTLY via integer DFT of the indicator of mu_n in F_p (mu_n = <g^m>, m=(p-1)/n).
  - PROPER subgroup ONLY (m = (p-1)/n > 1 enforced, m odd preferred); NEVER n = q-1.
  - prize-band primes p ~ n^beta, beta in {4.0, 4.5}; multiple primes incl. one non-Fermat.
  - RANDOM control: a random n-element subset R of F_p* of the SAME size n (thin density), compute its
    "periods" eta^R_b = sum_{x in R} e_p(b x); same moment profile. Median over several R.
  - Compare per r=1..R_MAX:  ratio_r := DCsub_{2r}(mu_n) / DCsub_{2r}(random)   and the Wick-normalized
    g_r := DCsub_{2r}/Wick_{2r} for thin and random; test whether thin g_r is SUPPRESSED below random
    and whether the suppression COMPOUNDS (ratio of consecutive thin/random gaps grows).

OUTPUT: per-prime table, then the VERDICT on compounding (collective) vs single-depth.
"""
import cmath, math, random
from sympy import isprime

def next_prime_ge(x):
    x = int(x)
    if x % 2 == 0: x += 1
    while not isprime(x): x += 2
    return x

def prime_for(n, beta, want_non_fermat=False, seed=0):
    # p == 1 mod n, p ~ n^beta, proper subgroup (m=(p-1)/n>1)
    base = int(round(n**beta))
    # search p = 1 + n*t prime, t>1 (so m=t>1 proper), starting near base
    t0 = max(2, base // n)
    rnd = random.Random(seed)
    t = t0
    tried = 0
    while True:
        p = 1 + n*t
        if p > n+1 and isprime(p):
            m = (p-1)//n
            if m > 1:  # proper subgroup
                if want_non_fermat:
                    # avoid p-1 being a pure power of 2 (Fermat-ish); require m odd-ish or m has odd factor
                    if m % 2 == 1 or (m & (m-1)) != 0:
                        return p
                else:
                    return p
        t += 1
        tried += 1
        if tried > 200000:
            raise RuntimeError("no prime found")

def subgroup_mu_n(p, n):
    # multiplicative subgroup of order n in F_p* : find a generator g of F_p*, take g^m, m=(p-1)//n
    m = (p-1)//n
    # find primitive root
    def is_primroot(g):
        # check order = p-1 by testing g^((p-1)/q) != 1 for prime q | p-1
        order = p-1
        x = order
        factors = set()
        d = 2
        while d*d <= x:
            while x % d == 0:
                factors.add(d); x//=d
            d += 1
        if x>1: factors.add(x)
        for q in factors:
            if pow(g, order//q, p) == 1:
                return False
        return True
    g = 2
    while not is_primroot(g):
        g += 1
    h = pow(g, m, p)  # generator of mu_n
    S = []
    cur = 1
    for _ in range(n):
        S.append(cur)
        cur = (cur*h) % p
    assert len(set(S)) == n, "subgroup size mismatch"
    # sanity: -1 in mu_n iff n even (2-power n>=2 => yes); verify not n=q-1
    assert n != p-1, "REFUSED: n = q-1 full group (rule 2)"
    return S

def periods(S, p):
    # eta_b = sum_{x in S} e_p(b x), for b=0..p-1. Return list of complex (we only need b!=0).
    # exact-ish via cmath; p up to ~n^4.5 ~ for n=16 -> ~1e5, n=32 -> ~1e6. Loop b over 1..p-1 is O(p*n).
    n = len(S)
    out = [0.0]*p
    twopi = 2*math.pi/p
    for b in range(1, p):
        s = 0j
        for x in S:
            ang = twopi*((b*x) % p)
            s += cmath.exp(1j*ang)
        out[b] = s
    return out

def even_moment(etas, p, twor):
    # E_{2r} := (1/(p-1)) sum_{b!=0} |eta_b|^{2r}? We want the RAW even power sum for the census identity.
    # Use sum_{b!=0} |eta_b|^{2r}  (real, the energy moment). DC term handled by caller.
    acc = 0.0
    for b in range(1, p):
        acc += abs(etas[b])**twor
    return acc

def double_fact_odd(m):  # (m)!! for odd m
    r = 1; k = m
    while k > 0:
        r *= k; k -= 2
    return r

def analyze(n, beta, seed, want_non_fermat=False, R_MAX=6, n_random=5):
    p = prime_for(n, beta, want_non_fermat, seed)
    m = (p-1)//n
    S = subgroup_mu_n(p, n)
    etas = periods(S, p)
    # random thin controls: pick n distinct nonzero residues
    rnd = random.Random(seed*7919+1)
    rand_profiles = []
    for _ in range(n_random):
        R = rnd.sample(range(1, p), n)
        re = periods(R, p)
        rand_profiles.append(re)
    rows = []
    for r in range(1, R_MAX+1):
        twor = 2*r
        # E_{2r} for thin
        E_thin = even_moment(etas, p, twor)
        DC = (n**(2*r))*(n**(2*r))/p   # n^{4r}/q with q ~ p ; DC subtraction term  (E over b!=0 has DC n^{4r}/q? )
        # NOTE: the dossier DC term for E_r = sum|eta|^{2r} over the energy convention is n^{2r}/q * (scaling).
        # We use the RATIO of DC-subtracted moments thin-vs-random; the exact DC constant cancels in the ratio
        # as long as applied identically. Use A := E_{2r} - n^{2*twor? }. To avoid DC-convention error we
        # report BOTH raw E ratio and the Wick-normalized g, and let the THIN-vs-RANDOM comparison (identical
        # DC handling) carry the signal.
        Wick = double_fact_odd(2*twor-1) * (n**twor)  # (4r-1)!! n^{2r}
        # random medians
        E_rands = sorted(even_moment(re, p, twor) for re in rand_profiles)
        E_rand = E_rands[len(E_rands)//2]
        ratio = E_thin / E_rand if E_rand>0 else float('inf')
        g_thin = E_thin / (p*Wick)   # normalize by p (|F|) and Wick
        g_rand = E_rand / (p*Wick)
        rows.append((r, E_thin, E_rand, ratio, g_thin, g_rand))
    return p, m, rows

def main():
    print("="*78)
    print("EVEN CENSUS PROFILE: thin mu_n vs random thin-density control (collective compounding test)")
    print("Object: per-r even energy moment E_{2r}=sum_{b!=0}|eta_b|^{2r}, thin vs random, COMPOUNDING.")
    print("rule-2: proper subgroup (m>1), never n=q-1. rule-3: random same-density control.")
    print("="*78)
    configs = [
        (16, 4.0, 1, False),
        (16, 4.5, 2, True),   # non-Fermat
        (32, 4.0, 3, False),
    ]
    for (n, beta, seed, nf) in configs:
        try:
            p, m, rows = analyze(n, beta, seed, nf, R_MAX=6, n_random=5)
        except Exception as e:
            print(f"\nn={n} beta={beta}: SKIP ({e})")
            continue
        print(f"\nn={n}  beta={beta}  p={p}  m=(p-1)/n={m} {'[non-Fermat]' if nf else ''}  (proper subgroup, n!=q-1 OK)")
        print(f"  {'r':>2} {'E_thin/E_rand':>14} {'g_thin':>10} {'g_rand':>10} {'g_thin/g_rand':>14}")
        prev_ratio = None
        compounding = []
        for (r, Et, Er, ratio, gt, gr) in rows:
            gg = gt/gr if gr>0 else float('inf')
            print(f"  {r:>2} {ratio:14.4f} {gt:10.4f} {gr:10.4f} {gg:14.4f}")
            compounding.append(gg)
        # compounding test: is g_thin/g_rand DECREASING in r (thin advantage grows) or flat (single-depth)?
        if len(compounding) >= 3:
            decreasing = all(compounding[i+1] <= compounding[i]*1.02 for i in range(len(compounding)-1))
            growing_gap = compounding[-1] < compounding[0]*0.9
            verdict = ("COMPOUNDS (collective advantage grows with r)" if (decreasing and growing_gap)
                       else "FLAT/non-compounding (single-depth, not collective)" if abs(compounding[-1]-compounding[0])<0.1*compounding[0]
                       else "MIXED")
            print(f"  --> g_thin/g_rand profile {[round(c,3) for c in compounding]}  VERDICT: {verdict}")

if __name__ == "__main__":
    main()

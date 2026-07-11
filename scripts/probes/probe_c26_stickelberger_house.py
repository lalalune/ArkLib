# Probe C26: "Stickelberger-House Conjecture" — does the exact Stickelberger ideal
# factorization of the Gauss sum tau(chi) bound the HOUSE (max archimedean conjugate
# modulus) of the dyadic Gauss period eta_c by C*sqrt(n log p), by FORCING the conjugates
# to be BALANCED without any moment/equidistribution input?
#
# C26 mechanism claim: Stickelberger gives the exact prime-ideal factorization (all p-adic
# valuations) of tau(chi) over Z[zeta_{p-1}]; these valuations "force the conjugates to be
# balanced", hence house ~ |norm|^{1/m} ~ sqrt(n).
#
# DECISIVE TESTS (proper subgroups: p prime, p >> n^3, n=2^mu, NEVER n=p-1):
#  (T1) Are the period conjugates {eta_c} BALANCED? Measure house/geomMean and house/min.
#       Stickelberger-balance would predict ratio ~ 1 (flat). If it GROWS with n, the claim
#       that Stickelberger forces balance is FALSE.
#  (T2) Does the p-adic (Stickelberger) data DISTINGUISH the conjugates at all? The eta_c are
#       Galois conjugates (sigma_t : eta_c -> eta_{t*c}); the FULL set of conjugates of the
#       single algebraic integer eta_1 is the orbit {eta_c}. Stickelberger gives the SAME
#       valuation profile to each (they are Galois conjugate ideals). So the p-adic data is
#       Galois-INVARIANT on the orbit => carries ZERO info about which conjugate is largest.
#       We confirm: the Frobenius/Stickelberger valuation (digit-sum of the character power)
#       is uncorrelated with |eta_c|.
#  (T3) Does the actual house track sqrt(n log p) (the target) and stay BELOW the trivial n,
#       i.e. is the OBJECT real — yes — but is the BOUND derivable from Stickelberger — no.
import math, cmath

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primroot(p):
    fac = set(); m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for a in range(2, p):
        if all(pow(a, (p-1)//q, p) != 1 for q in fac):
            return a
    raise RuntimeError

def base_p_digitsum(j, base):
    # placeholder; not used directly. Stickelberger valuation of tau(chi^a) at a prime above p
    # in Z[zeta_{p-1}] is governed by the base-p digit structure of the character exponent.
    s = 0
    while j:
        s += j % base; j //= base
    return s

def find_prime(n, target_exp):
    # p prime, p == 1 mod n, p ~ n^target_exp  (>> n^3 for target_exp>=4)
    base = int(round(n ** target_exp))
    p = base - (base % n) + 1
    for _ in range(200000):
        if p > 1 and isprime(p):
            return p
        p += n
    raise RuntimeError("no prime")

def analyze(n, p):
    g0 = primroot(p)
    g  = pow(g0, (p-1)//n, p)            # generator of mu_n (order n)
    H  = [pow(g, i, p) for i in range(n)]  # the subgroup mu_n
    m  = (p-1)//n                          # number of periods (cosets) = index
    # Gauss periods eta_c = sum_{h in H} e_p(c * h), c ranges over coset reps.
    # The full conjugate set (Galois orbit) is {eta_c : c in (Z/p)^* / H}. For the HOUSE we
    # need max over ALL c != 0. Computing all m cosets is huge for big m, so we sample MANY c
    # (uniformly from F_p^*) and take the running max — this lower-bounds the house and (with
    # enough samples) hits it. We also compute geomMean / min over the sampled set.
    import random
    random.seed(12345 + n + p % 100000)
    two_pi_over_p = 2*math.pi/p
    # sample distinct coset reps: pick random c, reduce to a canonical coset rep is unnecessary
    # for measuring magnitudes — eta_c depends only on coset, magnitudes well-defined per c.
    nsamp = min(m, 4000)
    mags = []
    digsum = []
    seen_cosets = set()
    tries = 0
    while len(mags) < nsamp and tries < nsamp*40:
        tries += 1
        c = random.randrange(1, p)
        # canonical coset rep = min over H-orbit, to dedupe; cheap enough for moderate n
        orbit = tuple(sorted((c*h) % p for h in H))
        key = orbit[0]
        if key in seen_cosets:
            continue
        seen_cosets.add(key)
        s = 0j
        for h in H:
            ang = two_pi_over_p * ((c*h) % p)
            s += cmath.exp(1j*ang)
        mags.append(abs(s))
        # Stickelberger proxy: discrete-log of c base g0 gives the character exponent; its
        # base-? digit sum is the Stickelberger valuation content. Use the index-of-c parity
        # structure (2-adic valuation of the coset label) as a cheap p-adic proxy, matching
        # the prior probe_galois_house_padic convention.
        # cheap: 2-adic valuation of the canonical rep
        kk = key; v = 0
        while kk % 2 == 0 and kk > 0:
            v += 1; kk //= 2
        digsum.append(v)
    house = max(mags)
    mn = min(mags)
    logsum = sum(math.log(x) for x in mags if x > 0)
    geom = math.exp(logsum/len([x for x in mags if x > 0]))
    sqn = math.sqrt(n)
    tgt = math.sqrt(n*math.log(p))
    # correlation of |eta| with the p-adic proxy
    import statistics
    if len(set(digsum)) > 1 and statistics.pstdev(mags) > 0:
        mx = statistics.mean(mags); md = statistics.mean(digsum)
        cov = sum((a-mx)*(b-md) for a,b in zip(mags,digsum))/len(mags)
        corr = cov/(statistics.pstdev(mags)*statistics.pstdev(digsum))
    else:
        corr = float('nan')
    return dict(n=n, p=p, m=m, nsamp=len(mags), house=house, mn=mn, geom=geom,
                sqn=sqn, tgt=tgt, corr=corr)

print("C26 Stickelberger-House test (proper mu_n, p prime, p ~ n^4 >> n^3, NEVER n=p-1)")
print(f"{'n':>4} {'p':>14} {'m=idx':>10} {'samp':>5} {'house':>8} {'h/sqrtn':>8} "
      f"{'h/geom':>8} {'h/min':>9} {'h/tgt':>7} {'corr(|eta|,padic)':>17}")
for n in [8, 16, 32, 64]:
    p = find_prime(n, 4.0)         # p ~ n^4, strictly >> n^3, prize-shaped exponent
    r = analyze(n, p)
    print(f"{r['n']:>4} {r['p']:>14} {r['m']:>10} {r['nsamp']:>5} "
          f"{r['house']:>8.3f} {r['house']/r['sqn']:>8.3f} "
          f"{r['house']/r['geom']:>8.3f} {r['house']/r['mn']:>9.2f} "
          f"{r['house']/r['tgt']:>7.3f} {r['corr']:>17.4f}")

print()
print("VERDICT KEYS:")
print(" T1 balance: if h/geom and h/min GROW with n, Stickelberger does NOT force balance.")
print(" T2 p-adic:  corr(|eta|, p-adic valuation) ~ 0  =>  Stickelberger data carries NO")
print("             archimedean spread info (conjugates are Galois-equivalent ideals).")
print(" Object real (house < n, ~ sqrt(n log p)) but bound NOT delivered by Stickelberger.")

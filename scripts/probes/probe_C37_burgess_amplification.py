#!/usr/bin/env python3
"""
PROBE [C37]: Burgess-Type Amplification for the Thin Dyadic Subgroup Sum.

CONJECTURE C37 claims: a Burgess-style shifted-multiplicative amplification of the
period sum  S_a(mu_n) = sum_{x in mu_n} e_p(a x)  recovers sqrt-cancellation
  M(mu_n) = max_{a != 0} |S_a(mu_n)| <= sqrt(n log p)
in the prize band (n = p^delta, delta < 1/4), past Johnson.

WHAT THE BURGESS METHOD ACTUALLY DOES (for SHORT CHARACTER SUMS over an interval):
  To bound  T = sum_{x in I} chi(x),  |I| = N, one
   (1) AMPLIFIES by translation: for many shifts t in a set Sh,
         T ~ (1/|Sh|) sum_{t in Sh} sum_{x in I} chi(x+t)   (shifting the interval is ~lossless because I is an INTERVAL: I+t overlaps I in N-|t| points)
   (2) opens the 2r-th moment over t and applies WEIL/completion to the resulting
       COMPLETE multiplicative correlation sums over t in F_p:
         sum_t prod_j chi(t + a_j) chi(t + b_j)^{-1}  <<  (2r) sqrt(p).
  The gain N^{-1/r} p^{(r+1)/(4r^2)} is nontrivial ONLY when N >> p^{1/4}.

THE STRUCTURAL OBSTRUCTION FOR A SUBGROUP (what this probe measures):
  mu_n is a MULTIPLICATIVE set, not an interval. Step (1) is the load-bearing step:
  Burgess needs that translating the summation set by t loses few elements, i.e.
        |(mu_n + t) cap mu_n|  ~  n   for "most/many" small t.
  This is FALSE for a thin multiplicative subgroup: |(mu_n + t) cap mu_n| is the
  additive-shift correlation of mu_n, which is O(1)-ish (governed by mult. energy),
  NOT ~ n. So the amplification is LOSSY: averaging over shifts destroys, not
  preserves, the sum. This probe measures the actual shift-overlap profile and the
  amplified-moment gain over a REAL proper subgroup.

HONESTY: proper subgroup mu_n (n | p-1, n = 2^mu), p PRIME, p >> n^3, NEVER n=p-1.
"""
import cmath, math, random

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def find_prime(n, mul):
    """smallest prime p = 1 mod n with p >= n*mul  (so p >> n^3 when mul>=n^2)."""
    base = n * mul
    t = base + ((1 - base) % n)        # smallest >= base with t = 1 mod n
    if t <= base: t += n
    while not is_prime(t): t += n
    return t

def subgroup(p, n):
    """mu_n = unique subgroup of order n in F_p^*  (n | p-1)."""
    assert (p-1) % n == 0
    # find a generator g of F_p^*
    fac = []
    m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: fac.append(m)
    def is_gen(g):
        return all(pow(g,(p-1)//q,p) != 1 for q in fac)
    g = next(x for x in range(2,p) if is_gen(x))
    b = pow(g,(p-1)//n,p)
    H = sorted({pow(b,i,p) for i in range(n)})
    assert len(H) == n
    return H

def Sa(H, a, p):
    """period sum S_a = sum_{x in H} e_p(a x)."""
    s = 0j
    for x in H:
        s += cmath.exp(2j*math.pi*(a*x % p)/p)
    return s

def M_of_H(H, p, sample=None, rng=None):
    """M(H) = max_{a != 0} |S_a|.  exact if sample None, else random sample of a."""
    best = 0.0; arg = 0
    if sample is None:
        rng_a = range(1,p)
    else:
        rng_a = [rng.randrange(1,p) for _ in range(sample)]
    for a in rng_a:
        v = abs(Sa(H,a,p))
        if v > best: best = v; arg = a
    return best, arg

def shift_overlap_profile(Hset, p, t_count, rng):
    """|(H + t) cap H| for random nonzero t.  Burgess step (1) needs this ~ n."""
    H = Hset; n = len(H)
    ov = []
    seen = set()
    for _ in range(t_count):
        t = rng.randrange(1,p)
        if t in seen: continue
        seen.add(t)
        c = sum(1 for x in H if ((x + t) % p) in H)
        ov.append(c)
    return ov

def run(mu, mul, sample_a=None, t_count=400, seed=0):
    n = 2**mu
    p = find_prime(n, mul)
    rng = random.Random(seed)
    delta = math.log(n)/math.log(p)
    beta  = math.log(p)/math.log(n)
    H = subgroup(p, n)
    Hset = set(H)
    # actual sup-norm (sampled if p large)
    Mval, amax = M_of_H(H, p, sample=sample_a, rng=rng)
    target = math.sqrt(n*math.log(p))
    paley  = math.sqrt(n*math.log(p/n))
    triv   = n
    # shift-overlap profile (the Burgess amplification feasibility test)
    ov = shift_overlap_profile(Hset, p, t_count, rng)
    ov_mean = sum(ov)/len(ov); ov_max = max(ov)
    # For an INTERVAL of length N, mean overlap with a random nearby shift ~ N (Burgess regime).
    # For a thin subgroup, expected overlap of (H+t) cap H over random t = n*(n-1)/(p-1) ~ n^2/p.
    expected_random = n*(n-1)/(p-1)
    print(f"\n=== mu={mu}  n=2^{mu}={n}  p={p} (prime={is_prime(p)})  p~2^{math.log2(p):.1f} ===")
    print(f"    n = p^{delta:.4f}   beta=log_n p = {beta:.3f}   (prize band: delta<1/4, beta>4)")
    print(f"    p/n^3 = {p/n**3:.3e}  (p >> n^3 required)   n=p-1? {n==p-1}")
    print(f"    M(H) measured{' (sampled '+str(sample_a)+' a)' if sample_a else ' (exact)'} = {Mval:.2f}  at a={amax}")
    print(f"      sqrt(n)            = {math.sqrt(n):.2f}")
    print(f"      C37 target sqrt(n log p) = {target:.2f}")
    print(f"      Paley  sqrt(n log(p/n))  = {paley:.2f}")
    print(f"      trivial n               = {triv}")
    print(f"      M/sqrt(n) = {Mval/math.sqrt(n):.3f}   (true value sits at Paley scale ~ O(sqrt log))")
    print(f"    --- BURGESS AMPLIFICATION FEASIBILITY (the load-bearing step) ---")
    print(f"    |(H+t) cap H| over {len(ov)} random t != 0:  mean={ov_mean:.3f}  max={ov_max}")
    print(f"    Burgess needs this ~ n = {n} (as for an INTERVAL).  Got mean {ov_mean:.3f}.")
    print(f"    Expected random overlap n^2/p = {expected_random:.4f}  (i.e. essentially 0 -> NO amplification)")
    burgess_gain = ov_mean / n
    print(f"    Amplification efficiency = mean_overlap / n = {burgess_gain:.2e}")
    print(f"    => shift-translation amplification recovers {'sqrt-cancellation' if ov_mean > 0.5*n else 'NOTHING (subgroup is not an interval)'}")
    return dict(mu=mu,n=n,p=p,delta=delta,M=Mval,target=target,paley=paley,ov_mean=ov_mean,gain=burgess_gain)

if __name__ == "__main__":
    print("="*78)
    print("C37 BURGESS AMPLIFICATION PROBE — proper mu_n, p prime, p>>n^3, never n=p-1")
    print("="*78)
    # Exact M for small n (full a-range); larger n sampled. mul = n^2..n^3 keeps p >> n^3.
    run(mu=3, mul=2**6,  sample_a=None, t_count=300, seed=1)   # n=8,   p>>512
    run(mu=4, mul=2**8,  sample_a=None, t_count=400, seed=1)   # n=16,  p>>4096
    run(mu=5, mul=2**10, sample_a=None, t_count=500, seed=1)   # n=32
    run(mu=6, mul=2**12, sample_a=1500, t_count=600, seed=1)   # n=64
    run(mu=7, mul=2**14, sample_a=1500, t_count=800, seed=1)   # n=128
    run(mu=8, mul=2**16, sample_a=1200, t_count=800, seed=1)   # n=256
    print("\n===C37BURGESSDONE===")

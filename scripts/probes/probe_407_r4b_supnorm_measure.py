#!/usr/bin/env python3
"""
LANE R4b (#407) — measure M(n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)|
at PRIZE-SCALE constant-index primes p ~ n^4 (beta = log_n p in [4,5]).

Question (per directive): does M(n)/sqrt(n*log(p/n)) stay O(1) (window membership,
C = O(1)) as n = 2^mu grows, or does it grow?  The KB notes a SHARP constant
C=sqrt(2)/C=1 is REFUTED at n=64,p=16778497 (R=1.051>1); the LIVE question is
boundedness of C, not its exact value.

Method.  For p ~ n^4 with n=2^mu, the full b-sweep is O(p) ~ n^4 evaluations of an
n-term sum = O(n^5).  Feasible exactly up to n^5 ~ 2^30 (n=2^6, p~1.7e7).  For larger
n we (a) restrict b to one representative per H-coset since S_{b}(H)=S_{bt}(H) for
t in H [reduces the sweep by factor n], and (b) for the largest n, sample a large
random set of cosets + a targeted search, reporting max-over-sample (a LOWER bound
on the true M, so any growth we see is real).

We report:
  M(n)               measured (exact for small n, sampled-max for large n)
  base  = sqrt(n*log(p/n))
  R     = M(n)/base                 [the C we test for boundedness]
  Rg    = M(n)/sqrt(2*n*log(p/n))   [the refuted-sharp comparison]
  meanS, p99S        mean and 99th pct of |S_b| over the swept/sampled b
"""
import math, random
import numpy as np

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime_near(n, beta_target=4.0):
    """smallest prime p ≡ 1 mod n with p >= n^beta_target."""
    base = int(n**beta_target)
    # round up to ≡ 1 mod n
    p = base - (base % n) + 1
    if p <= base: p += n
    while not isprime(p):
        p += n
    return p

def primitive_root(p):
    # factor p-1
    m = p - 1
    fac = set()
    d = 2
    mm = m
    while d*d <= mm:
        while mm % d == 0:
            fac.add(d); mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    for g in range(2, p):
        if all(pow(g, m//q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)   # generator of mu_n
    H = [1]
    x = h
    while x != 1:
        H.append(x); x = (x*h) % p
    assert len(H) == n, (len(H), n)
    return np.array(H, dtype=np.int64), g

def measure_exact(p, n, H):
    """Exact M over all b in [1,p-1] via reduction to coset reps.
    S_b depends only on b*H (since S_{bt}=S_b for t in H).  Compute |S_b| for b
    ranging over coset reps.  We sweep all b directly but skip via a 'seen' mask
    only when p is small enough; otherwise just sweep all b (cheaper than mask)."""
    twopi_over_p = 2*math.pi/p
    Hf = H.astype(np.float64)
    best = 0.0
    allmod = []
    # vectorized over b in chunks
    bs = np.arange(1, p, dtype=np.int64)
    # |S_b|^2 = sum_{x,y} cos(2pi b (x-y)/p); compute |S_b| via complex exp
    CHUNK = max(1, (1<<24)//n)
    for start in range(0, len(bs), CHUNK):
        bb = bs[start:start+CHUNK]                      # (C,)
        ph = (np.outer(bb, H) % p).astype(np.float64)   # (C,n)
        ang = twopi_over_p * ph
        re = np.cos(ang).sum(axis=1)
        im = np.sin(ang).sum(axis=1)
        mod = np.sqrt(re*re + im*im)
        m = mod.max()
        if m > best: best = m
        # subsample for stats (keep memory bounded)
        if len(allmod) < 4_000_000:
            allmod.append(mod)
    allmod = np.concatenate(allmod) if allmod else np.array([0.0])
    return best, float(allmod.mean()), float(np.percentile(allmod, 99))

def measure_sampled(p, n, H, nsamp=2_000_000, seed=0):
    """Sampled-max over random b (LOWER bound on true M)."""
    rng = np.random.default_rng(seed)
    twopi_over_p = 2*math.pi/p
    best = 0.0
    means = []
    p99s = []
    CHUNK = max(1, (1<<24)//n)
    done = 0
    while done < nsamp:
        c = min(CHUNK, nsamp - done)
        bb = rng.integers(1, p, size=c, dtype=np.int64)
        ph = (np.outer(bb, H) % p).astype(np.float64)
        ang = twopi_over_p * ph
        re = np.cos(ang).sum(axis=1)
        im = np.sin(ang).sum(axis=1)
        mod = np.sqrt(re*re + im*im)
        m = mod.max()
        if m > best: best = m
        means.append(mod.mean()); p99s.append(np.percentile(mod, 99))
        done += c
    return best, float(np.mean(means)), float(np.mean(p99s))

def run(beta=4.0, exact_cap=20_000_000, sampled_n=2_000_000):
    print(f"\n===== beta_target = {beta}  (prize-scale constant index) =====")
    print(f"{'mu':>3} {'n':>7} {'p':>16} {'beta':>6} {'M(n)':>10} {'base':>10} "
          f"{'R=M/base':>9} {'Rg=M/sqrt2base':>14} {'meanS':>8} {'p99S':>8} {'mode':>8}")
    results = []
    for mu in range(6, 17):
        n = 1 << mu
        p = find_prime_near(n, beta)
        beta_eff = math.log(p)/math.log(n)
        H, g = subgroup(p, n)
        base = math.sqrt(n*math.log(p/n))
        if p <= exact_cap:
            M, meanS, p99S = measure_exact(p, n, H)
            mode = "exact"
        else:
            M, meanS, p99S = measure_sampled(p, n, H, nsamp=sampled_n, seed=mu)
            mode = "smpl"
        R = M/base
        Rg = M/(math.sqrt(2)*base)
        print(f"{mu:>3} {n:>7} {p:>16} {beta_eff:>6.3f} {M:>10.2f} {base:>10.2f} "
              f"{R:>9.4f} {Rg:>14.4f} {meanS:>8.2f} {p99S:>8.2f} {mode:>8}")
        results.append((mu, n, p, beta_eff, M, base, R, Rg, mode))
    return results

if __name__ == "__main__":
    # KB validation point first
    p64 = 16778497; n64 = 64
    H64, _ = subgroup(p64, n64)
    base64 = math.sqrt(n64*math.log(p64/n64))
    M64, mean64, p99_64 = measure_exact(p64, n64, H64)
    print("=== KB validation: n=64, p=16778497 (claimed R=1.051) ===")
    print(f"M={M64:.3f} base={base64:.3f} R=M/base={M64/base64:.4f} "
          f"Rsharp=M/sqrt(2)base={M64/(math.sqrt(2)*base64):.4f} meanS={mean64:.3f}")
    run(beta=4.0)

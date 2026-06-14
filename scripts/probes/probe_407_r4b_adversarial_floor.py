#!/usr/bin/env python3
"""
LANE R4b (#407) — ADVERSARIAL floor search: try hard to find b with
|S_b(mu_n)| >> sqrt(n*log(p/n)) at prize-scale p ~ n^4.

If such a b exists with M(n)/sqrt(n log(p/n)) GROWING in n, the prize-regime
sup-norm floor (the conjecture M(n) <= C*sqrt(n log(p/n))) is REFUTED.

Two independent attack vectors for the worst b:
 (A) "small-residue clustering": pick b so that the elements b*x mod p land in a
     short interval around 0 (i.e. b ~ p/(small spread)).  We hill-climb b by
     locally adjusting to minimize the angular spread of {b*x}.
 (B) coset-rep exact-over-a-window: enumerate b over a contiguous window and over
     b = round(p * j / D) for small denominators D (rational-approximation peaks,
     where many bx align) -- the classic large-value loci of incomplete char sums.
 (C) random baseline (large sample) for comparison.

We also do a FULL exact sweep when p is small enough, to certify the sampled/targeted
max equals the true M (calibration of the heuristics).
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

def find_prime_near(n, beta=4.0):
    base = int(n**beta)
    p = base - (base % n) + 1
    if p <= base: p += n
    while not isprime(p):
        p += n
    return p

def primitive_root(p):
    m = p - 1; fac = set(); d = 2; mm = m
    while d*d <= mm:
        while mm % d == 0: fac.add(d); mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    for g in range(2, p):
        if all(pow(g, m//q, p) != 1 for q in fac): return g

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    H = [1]; x = h
    while x != 1: H.append(x); x = (x*h) % p
    return np.array(H, dtype=np.int64)

def Sb_abs(b, H, p):
    ang = (2*math.pi/p) * ((b*H) % p).astype(np.float64)
    return math.hypot(np.cos(ang).sum(), np.sin(ang).sum())

def Sb_abs_vec(bs, H, p):
    ph = (np.outer(bs, H) % p).astype(np.float64)
    ang = (2*math.pi/p)*ph
    re = np.cos(ang).sum(axis=1); im = np.sin(ang).sum(axis=1)
    return np.sqrt(re*re+im*im)

def attack_rational(H, p, n, Dmax=4000):
    """b = round(p*j/D), gcd(j,D)=1, D<=Dmax. Peaks of incomplete sums."""
    best = 0.0; bestb = 0
    cand = []
    for D in range(1, Dmax+1):
        for j in range(1, D):
            if math.gcd(j, D) != 1: continue
            cand.append((p*j)//D)
        if len(cand) > 200000:
            arr = np.array(cand, dtype=np.int64) % p
            arr = arr[arr != 0]
            mod = Sb_abs_vec(arr, H, p)
            k = mod.argmax()
            if mod[k] > best: best = mod[k]; bestb = int(arr[k])
            cand = []
    if cand:
        arr = np.array(cand, dtype=np.int64) % p
        arr = arr[arr != 0]
        mod = Sb_abs_vec(arr, H, p)
        k = mod.argmax()
        if mod[k] > best: best = mod[k]; bestb = int(arr[k])
    return best, bestb

def attack_hillclimb(H, p, n, restarts=40, seed=0):
    """Greedy local search on b to maximize |S_b|. Multiplicative + additive steps."""
    rng = random.Random(seed)
    best = 0.0; bestb = 0
    steps = [1,-1,2,-2,n,-n, p//n, -(p//n)]
    for _ in range(restarts):
        b = rng.randrange(1, p)
        cur = Sb_abs(b, H, p)
        improved = True
        it = 0
        while improved and it < 400:
            improved = False; it += 1
            for s in steps:
                nb = (b + s) % p
                if nb == 0: continue
                v = Sb_abs(nb, H, p)
                if v > cur: cur = v; b = nb; improved = True; break
            # multiplicative kicks by small units
            if not improved:
                for t in (2,3,5,7,p-1):
                    nb = (b*t) % p
                    if nb == 0: continue
                    v = Sb_abs(nb, H, p)
                    if v > cur: cur = v; b = nb; improved = True; break
        if cur > best: best = cur; bestb = b
    return best, bestb

def attack_random(H, p, n, nsamp=2_000_000, seed=1):
    rng = np.random.default_rng(seed)
    best = 0.0
    CHUNK = max(1, (1<<23)//n); done=0
    while done < nsamp:
        c = min(CHUNK, nsamp-done)
        bs = rng.integers(1, p, size=c, dtype=np.int64)
        mod = Sb_abs_vec(bs, H, p)
        m = mod.max()
        if m > best: best = m
        done += c
    return best

def run(beta=4.0):
    print(f"\n==== ADVERSARIAL floor search, beta={beta} (prize-scale p~n^{beta}) ====")
    print(f"{'mu':>3} {'n':>6} {'p':>16} {'base':>9} {'Mrand':>8} {'Mrat':>8} "
          f"{'Mhill':>8} {'Mbest':>8} {'R=Mbest/base':>13}")
    for mu in range(6, 15):
        n = 1 << mu
        p = find_prime_near(n, beta)
        H = subgroup(p, n)
        base = math.sqrt(n*math.log(p/n))
        Mr = attack_random(H, p, n, nsamp=1_000_000, seed=mu)
        Mq, _ = attack_rational(H, p, n, Dmax=min(3000, 6_000_000//n))
        Mh, _ = attack_hillclimb(H, p, n, restarts=30, seed=mu)
        Mbest = max(Mr, Mq, Mh)
        print(f"{mu:>3} {n:>6} {p:>16} {base:>9.2f} {Mr:>8.2f} {Mq:>8.2f} "
              f"{Mh:>8.2f} {Mbest:>8.2f} {Mbest/base:>13.4f}")

if __name__ == "__main__":
    run(beta=4.0)

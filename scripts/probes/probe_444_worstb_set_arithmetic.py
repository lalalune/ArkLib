#!/usr/bin/env python3
"""
probe_444_worstb_set_arithmetic.py  (#444, door-(iv) Lane 1)

THE UN-ANSWERED LANE-1 QUESTION (brief, Shaw-value essay 2026-06-18):
  "what arithmetic of b selects the worst coset alignment? is the worst-b SET itself structured?"

Prior work (DISPROOF_LOG 2026-06-15) ruled out ILO/anti-concentration as a *bulk* lever
(thin mu_n concentrates WORSE than random -> M_thin >= M_rand). That measured the MAGNITUDE
M(n)=max_b|eta_b|. It did NOT characterize the *argmax SET* W = {b!=0 : |eta_b| >= (1-tau)*M(n)}.

If W is itself ARITHMETICALLY STRUCTURED (union of few mu_n-cosets, an interval/AP, a
multiplicative orbit) then a structure-sensitive (non-sum-product, non-moment) bound could
grip it. If W is generic/spread, the door-(iv) "exploit worst-b arithmetic" hope is weaker.

NO moment, NO completion, NO Lean. Prize regime: PROPER 2-power subgroup mu_n < F_p^*,
p == 1 mod n, m=(p-1)/n preferentially ODD, NEVER n=q-1. Vectorized (numpy) b-sweep.
"""
import math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def find_prime_thin(n, beta, odd_m=True):
    target = int(n**beta)
    p = target - (target % n) + 1
    if p <= target: p += n
    best_any = None
    for _ in range(400000):
        if isprime(p):
            mm = (p-1)//n
            if mm % 2 == 1 or not odd_m:
                return p
            if best_any is None: best_any = p
        p += n
    return best_any

def factor(x):
    fs = set(); d = 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x//=d
        d += 1
    if x>1: fs.add(x)
    return fs

def generator(p):
    pm1 = p-1; fs = factor(pm1)
    for cand in range(2, p):
        if all(pow(cand, pm1//q, p) != 1 for q in fs):
            return cand
    return None

def subgroup(n, p, g):
    h = pow(g, (p-1)//n, p)
    mu = sorted(set(pow(h, i, p) for i in range(n)))
    return mu

def eta_abs_sweep(mu, p):
    """vectorized |eta_b| for all b in 1..p-1. returns numpy array indexed by b (0 unused)."""
    bs = np.arange(0, p, dtype=np.int64)
    acc = np.zeros(p, dtype=np.complex128)
    twopi = 2*math.pi
    for x in mu:
        ph = (bs * x) % p
        acc += np.exp(1j * twopi * ph / p)
    return np.abs(acc)

def longest_ap(S, p):
    Sset = set(S); best = 1; Sl = sorted(S)
    for i in range(len(Sl)):
        for j in range(i+1, len(Sl)):
            d = (Sl[j]-Sl[i]) % p
            if d == 0: continue
            length = 2; nxt = (Sl[j]+d) % p
            while nxt in Sset:
                length += 1; nxt = (nxt+d) % p
            if length > best: best = length
    return best

def analyze(n, beta):
    p = find_prime_thin(n, beta)
    if p is None:
        print(f"  [n={n} beta={beta}] no prime", flush=True); return
    g = generator(p)
    mu = subgroup(n, p, g)
    if len(mu) != n:
        print(f"  [n={n}] |mu|={len(mu)}!=n skip", flush=True); return
    mm = (p-1)//n
    av = eta_abs_sweep(mu, p)
    av[0] = -1.0  # exclude b=0
    M = av.max(); sqrtn = math.sqrt(n)
    print(f"  n={n} p={p} m={mm}{' ODD' if mm%2 else ' even'} beta_eff={math.log(p)/math.log(n):.2f}  M={M:.4f} M/sqrtn={M/sqrtn:.3f}", flush=True)
    muset = set(mu)
    for tau in (0.02, 0.05, 0.10):
        thr = (1-tau)*M
        W = [int(b) for b in np.nonzero(av >= thr)[0]]
        Wset = set(W); frac = len(W)/(p-1)
        orbit_closed = all(((b*x) % p) in Wset for b in W for x in mu)
        cosets = set()
        for b in W:
            cosets.add(min((b*x) % p for x in mu))
        ncos = len(cosets)
        neg_closed = all(((-b) % p) in Wset for b in W)
        sq_closed  = all(((b*b) % p) in Wset for b in W)
        g_closed   = all(((b*g) % p) in Wset for b in W)
        dbl = ap = None
        if len(W) <= 500:
            sums = set((a+b) % p for a in W for b in W)
            dbl = len(sums)/len(W)
            ap = longest_ap(W, p)
        extra = f"  |W+W|/|W|={dbl:.1f} longestAP={ap}" if dbl is not None else "  (|W|>500: skip add)"
        print(f"    tau={tau:.0%}: |W|={len(W):5d} frac={frac:.4f}  #cosets={ncos} (|W|/n~{len(W)/n:.1f})  "
              f"muOrbit={orbit_closed} negSym={neg_closed} sq={sq_closed} mulg={g_closed}{extra}", flush=True)
    bstar = int(av.argmax())
    negstar_near = av[(-bstar) % p] >= 0.98*M
    print(f"    worst b*={bstar}  -b*={(-bstar)%p}  (-b* near-max?={bool(negstar_near)})", flush=True)

if __name__ == "__main__":
    print("=== probe_444_worstb_set_arithmetic: structure of near-max set W ===", flush=True)
    for n in (8, 16, 32):
        for beta in (4.0, 4.5):
            analyze(n, beta)
    print("=== done ===", flush=True)

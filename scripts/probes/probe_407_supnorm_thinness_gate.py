#!/usr/bin/env python3
"""
THE CORE QUANTITY, rule-3 gate: is the BGK SUP-NORM M(n)=max_{b≠0}|η_b| THINNESS-ESSENTIAL?

CORE asks M(n) <= C*sqrt(n*log(p/n)). The even-moment ENERGY face is NOT thinness-essential
(probe_407_parseval_dcsub_deep: thin == neg-closed-random at all r). But the SUP is a single-frequency
extremal quantity, NOT the aggregate energy -- it could be thin-essential where the energy is not.
This is the decisive rule-3 test of the ACTUAL CORE object (not a moment proxy).

Compare, at the SAME size n and SAME negation-closure (so the control isolates the genuine 2-power
subgroup structure from mere neg-closure / size):
  M_thin = max_{b!=0} |eta_b(mu_n)|         (mu_n = thin 2-power subgroup)
  M_rand = max_{b!=0} |eta_b(R)|, R = n/2 antipodal pairs {+/-t}, t random  (neg-closed, same size)
and ALSO a generic random set (not neg-closed) for context.

VERDICT logic (rule-3):
  - if M_thin < M_rand robustly (thin sup SMALLER): thinness HELPS the sup -> a LIVE lever for CORE.
  - if M_thin >= M_rand: the sup face is ALSO walled (thin no better, or worse) -> mapped wall.
We ALSO compare to the CORE target sqrt(n log(p/n)) and to sqrt(n) (Johnson/random scale) to see which
side the thin sup sits on.

Exact mod-p: eta_b = sum_{y in mu_n} omega^{b y}, computed EXACTLY as a complex via integer phases.
We use float for |.| (the sup is a real comparison; rule-6: cross-check with a second prime). PROPER
mu_n (m=(p-1)/n>=2), NEVER n=q-1, prize-band p~n^beta, multiple primes incl. Fermat.
"""
import sys, math, cmath, argparse, random
import numpy as np

def build_field(n, beta, min_m=2, seed_off=0):
    import sympy
    lo = max(int(n**beta), n*min_m+1)
    p = lo - (lo % n) + 1
    skip = seed_off
    while True:
        if p > n*min_m and sympy.isprime(p):
            if skip == 0: break
            skip -= 1
        p += n
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    assert pow(h,n,p)==1 and all(pow(h,d,p)!=1 for d in range(1,n))
    mu = [pow(h,i,p) for i in range(n)]
    return p, mu, (p-1)//n

def supnorm(elts, p):
    # M = max_{b!=0} |sum_{y in elts} omega^{b y}|, omega=e^{2pi i/p}. b ranges over F_p*.
    # full b-sweep is O(p*|elts|); for p~n^4 and n<=64 that's up to ~6.7e7*64 -- too big at n=64.
    # Use numpy: build phase matrix only over a representative b-set. The sup over ALL b!=0 is needed.
    # Vectorize: for each b, sum over y. Do it in blocks of b.
    e = np.array(elts, dtype=np.int64)
    best = 0.0; argb = 0
    BLK = 200000
    b = 1
    while b < p:
        bb = np.arange(b, min(b+BLK, p), dtype=np.int64)
        # phases: (len(bb), len(e)) = exp(2pi i (bb_outer e)/p). matrix may be large; cap BLK.
        ph = np.exp(2j*math.pi*((bb[:,None]*e[None,:]) % p)/p)
        s = np.abs(ph.sum(axis=1))
        j = int(np.argmax(s))
        if s[j] > best: best = float(s[j]); argb = int(bb[j])
        b += BLK
    return best, argb

def main(n, beta, ndraws=8):
    target_const = None
    print(f"=== n={n} beta={beta} : BGK sup-norm thinness gate ===", flush=True)
    for off in range(2):  # two primes (rule-6 q-invariance of the VERDICT)
        p, mu, m = build_field(n, beta, seed_off=off)
        Mthin, bth = supnorm(mu, p)
        # neg-closed random controls
        nc = []
        for _ in range(ndraws):
            half = random.sample(range(1, p), n//2)
            R = []
            for t in half: R += [t, (p-t)%p]
            Mr,_ = supnorm(R, p)
            nc.append(Mr)
        # generic (not neg-closed) random controls
        gen = []
        for _ in range(ndraws):
            R = random.sample(range(1, p), n)
            Mr,_ = supnorm(R, p)
            gen.append(Mr)
        nc.sort(); gen.sort()
        Mnc = nc[len(nc)//2]; Mgen = gen[len(gen)//2]
        sqrtn = math.sqrt(n); core_t = math.sqrt(n*math.log(p/n)); full = n
        print(f" p={p} (log_n p={math.log(p)/math.log(n):.2f}, m={m}):", flush=True)
        print(f"   M_thin            = {Mthin:.3f}   (worst b={bth}, b/n-ratio gcd={math.gcd(bth,p)})", flush=True)
        print(f"   M_neg-closed-rand = {Mnc:.3f}  [min {nc[0]:.2f} max {nc[-1]:.2f}]", flush=True)
        print(f"   M_generic-rand    = {Mgen:.3f}  [min {gen[0]:.2f} max {gen[-1]:.2f}]", flush=True)
        print(f"   refs: sqrt(n)={sqrtn:.3f}  sqrt(n log(p/n))={core_t:.3f}  n={full}", flush=True)
        rnc = Mthin/Mnc if Mnc else float('inf'); rgen = Mthin/Mgen if Mgen else float('inf')
        vnc = "thin<negrand (HELPS)" if rnc<0.97 else ("thin==negrand (WALLED)" if rnc<1.03 else "thin>negrand (WORSE)")
        print(f"   ratio thin/neg-rand = {rnc:.3f} [{vnc}] ; thin/gen-rand = {rgen:.3f}", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--draws", type=int, default=8)
    a = ap.parse_args()
    main(a.n, a.beta, a.draws)

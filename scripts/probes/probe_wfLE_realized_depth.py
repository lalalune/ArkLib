#!/usr/bin/env python3
"""
wf-LE (#407): REALIZED worst-case norm of a depth-t (#S=t) subset of n-th roots,
n=2^a, via float product over primitive roots (fast). Goal: the true t-exponent.

|N(Sigma_S)| = prod_{w primitive n-th root} |Sigma_S(w)|.
For n=2^a primitive roots are w = exp(2pi i k/n), k odd. Sigma_S(w)=sum_{j in S} w^j.

We heavy-search the worst t-subset (random + greedy) and report realized log2|N|.
Compare to:  L2 bound (n/4)*log2(2t)  and  realized-full-set (n/2-1)^{n/4}.
Key question: does realized depth-t norm exponent  ~  (n/2)*0.5*log2(t)  (sqrt-cancellation,
i.e. each |Sigma_S(w)| ~ sqrt(t) typical => prod ~ t^{phi/2} = t^{n/4})? If so realized
worst depth-t ~ t^{n/4} = 2^{(n/4) log2 t}, which at n=2^30 is 2^{2^28 * log2 t} >> p for any t>=2.
"""
import numpy as np, math, random

def primitive_roots(n):
    ks = [k for k in range(n) if k % 2 == 1]  # n=2^a: primitive <=> odd
    return np.exp(2j*np.pi*np.array(ks)/n)

def lognorm(S, W):
    # log2 |prod_w sum_{j in S} w^j|
    vals = np.zeros(len(W), dtype=complex)
    for j in S:
        vals += W**j
    a = np.abs(vals)
    if np.any(a == 0):
        return -np.inf
    return float(np.sum(np.log2(a)))

def worst_depth_t(n, t, tries=4000):
    W = primitive_roots(n)
    best = -np.inf; bS=None
    for _ in range(tries):
        S = random.sample(range(n), t)
        v = lognorm(S, W)
        if v > best: best=v; bS=S
    return best, bS

if __name__ == "__main__":
    print("realized worst depth-t norm (log2) vs t^{n/4} prediction and L2 bound")
    for n in [32, 64]:
        print(f"  n={n} (n/4={n//4}):")
        print(f"    {'t':>3} {'realized':>10} {'t^(n/4)':>10} {'L2(2t)^(n/4)':>13} {'real/t^(n/4)':>13}")
        for t in [2,3,4,6,8,12,16]:
            if t > n: continue
            best, bS = worst_depth_t(n, t)
            pred = (n/4)*math.log2(t) if t>0 else 0
            l2 = (n/4)*math.log2(2*t)
            ratio = best/pred if pred>0 else float('nan')
            print(f"    {t:>3} {best:10.3f} {pred:10.3f} {l2:13.3f} {ratio:13.4f}")

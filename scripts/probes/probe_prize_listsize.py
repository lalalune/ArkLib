#!/usr/bin/env python3
"""
THE decisive measurement: sub-Johnson list size of explicit smooth-domain
Reed-Solomon codes in the prize (deep) band.

Issue #389: the whole deep-band MCA programme reduces to ExplainableCoreSupply
= bound the number of RS codewords (deg < k) agreeing with a word w (NOT a
codeword) on >= k+m+1 points, in the sub-Johnson range, by B subexponential
in C(n,k+m+1)/q^m.

Equivalently: the RS list size of w at agreement radius a = k+m+1, for
smooth domain mu_n in F_p. Johnson radius: agreement ~ sqrt(k*n). Deep band:
a between Johnson and k (i.e. k < a < sqrt(kn) roughly -> m from ~0 up).

This probe COMPUTES the exact list size for smooth-domain RS at small n,
swept over agreement thresholds a, for adversarially-chosen w (and random w),
to find: (1) is the list small (O(1)/poly) for SMOOTH domains in the deep
band, or does it blow up? (2) any structural pattern (group action, multiplicity)
suggesting a closed bound. The answer dictates the conjecture.
"""
import itertools, random
from collections import Counter

def smooth_domain(p, n):
    # need n | p-1; mu_n = <g^((p-1)/n)>
    assert (p-1) % n == 0
    for cand in range(2, p):
        h = pow(cand, (p-1)//n, p)
        if all(pow(h, j, p) != 1 for j in range(1, n)) and pow(h, n, p) == 1:
            return [pow(h, j, p) for j in range(n)]
    raise RuntimeError("no generator")

def all_rs_codewords(D, p, k):
    """all evaluations of deg<k polys on D (q^k of them) - feasible for small q^k."""
    n = len(D)
    for coeffs in itertools.product(range(p), repeat=k):
        yield tuple(sum(coeffs[t]*pow(x,t,p) for t in range(k)) % p for x in D)

def list_size(D, p, k, w, a):
    """# deg<k codewords agreeing with w on >= a points."""
    cnt = 0; reps = []
    for cw in all_rs_codewords(D, p, k):
        agree = sum(1 for i in range(len(D)) if cw[i] == w[i])
        if agree >= a:
            cnt += 1
            if len(reps) < 5: reps.append(agree)
    return cnt

# small smooth instances where q^k is enumerable
# (p, n, k): rate rho=k/n, Johnson agreement ~ sqrt(k n)
CASES = [
    (13, 12, 2),   # rho=1/6, n=12, johnson agree ~ sqrt(24)=4.9
    (17, 16, 2),   # rho=1/8, johnson ~ sqrt(32)=5.7
    (11, 10, 2),
]
random.seed(11)
for (p, n, k) in CASES:
    if n != (n if (p-1)%n==0 else -1): 
        print(f"skip ({p},{n},{k}): n nmid p-1"); continue
    D = smooth_domain(p, n)
    import math
    johnson_a = math.isqrt(k*n)
    print(f"\n=== p={p} n={n} k={k} rho={k}/{n}={k/n:.3f}  Johnson agree~{johnson_a} ===")
    # adversarial w: a deg-k poly's evals perturbed (forces near-codeword structure)
    # try: w = evals of a degree-k (just above) poly -> structured
    for desc, w in [
        ("random", tuple(random.randrange(p) for _ in range(n))),
        ("deg-k poly evals", tuple(sum(random.randrange(p)*pow(x,t,p) for t in range(k+1))%p for x in D)),
    ]:
        # ensure w not a codeword (deg<k): check by list at a=n
        row=[]
        for a in range(k+1, min(johnson_a+3, n)+1):
            ls = list_size(D, p, k, w, a)
            row.append((a, ls))
        print(f"  w={desc}: (agree a, #list) = {row}")

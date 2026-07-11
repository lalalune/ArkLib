#!/usr/bin/env python3
"""
probe_dooriv_multiform_smallball_blind.py (#444, door-(iv) Lane 1)
PROBE-FIRST validation: a SYSTEM of m additive-linear forms on the phase set S_b = b*mu_n
has dilation-invariant JOINT fiber counts. This is the genuine multi-dimensional Halász/
Littlewood-Offord small-ball lever (vector target), NOT a single form.

Test: jointFiberCount(S, A, t) = #{ v in S^k : A @ v = t }  (A: m x k coeff matrix, t in F^m).
Claim: jointFiberCount(lam*S, A, lam*t) = jointFiberCount(S, A, t) for lam != 0.
Validate on PROPER 2-power mu_n < F_p*, p >> n^3, never n=q-1.
"""
import itertools, math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def find_prime(n, beta):
    # p == 1 mod n, p ~ n^beta, p >> n^3, m=(p-1)/n preferentially odd
    target = int(n**beta)
    k = max(2, target // n)
    while True:
        p = k*n + 1
        if p > n**3 and isprime(p):
            m = (p-1)//n
            return p
        k += 1

def muN(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of mu_n
    S = set()
    v = 1
    for _ in range(n):
        S.add(v); v = (v*h) % p
    assert len(S) == n, (len(S), n)
    return sorted(S)

def primitive_root(p):
    if p == 2: return 1
    phi = p-1
    facs = set()
    x = phi
    d = 2
    while d*d <= x:
        if x % d == 0:
            facs.add(d)
            while x % d == 0: x//=d
        d += 1
    if x > 1: facs.add(x)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs):
            return g
    raise RuntimeError

def joint_fiber_count(S, A, t, p):
    # A: list of m rows, each row length k; t: list len m; v ranges over S^k
    m = len(A); k = len(A[0])
    cnt = 0
    for v in itertools.product(S, repeat=k):
        ok = True
        for r in range(m):
            s = sum(A[r][j]*v[j] for j in range(k)) % p
            if s != (t[r] % p):
                ok = False; break
        if ok: cnt += 1
    return cnt

import random
random.seed(7)
print(f"{'n':>4} {'p':>10} {'k':>2} {'m':>2}  {'#targets':>8}  all_match")
for (n, beta) in [(8,4.0),(16,4.0),(8,5.0)]:
    p = find_prime(n, beta)
    S = muN(p, n)
    # dilate by a random nonzero lam, and by b1,b2
    k = 3; m = 2
    A = [[random.randrange(1,p) for _ in range(k)] for _ in range(m)]
    lams = [random.randrange(1,p) for _ in range(4)]
    # build dilated sets
    allok = True
    ntargets = 0
    # sample targets t in F^m: use sums of actual tuples to hit nonempty fibers + a few random
    base_targets = set()
    for v in itertools.product(S, repeat=k):
        t = tuple(sum(A[r][j]*v[j] for j in range(k)) % p for r in range(m))
        base_targets.add(t)
        if len(base_targets) > 30: break
    targs = list(base_targets)[:20] + [tuple(random.randrange(p) for _ in range(m)) for _ in range(5)]
    ntargets = len(targs)
    for lam in lams:
        Sl = sorted((lam*x) % p for x in S)
        for t in targs:
            tl = tuple((lam*ti) % p for ti in t)
            c0 = joint_fiber_count(S, A, list(t), p)
            cl = joint_fiber_count(Sl, A, list(tl), p)
            if c0 != cl:
                allok = False
                print(f"  MISMATCH lam={lam} t={t}: {c0} vs {cl}")
    print(f"{n:>4} {p:>10} {k:>2} {m:>2}  {ntargets:>8}  {allok}")

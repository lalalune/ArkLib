# probe_407_k2_sstar_formula_break.py  (#407)
# THE k=2 over-determined far-line incidence s* sweep: tests whether the in-tree
# delta* formula (HEAD b66b7f769) delta* = 1/2 + (1/(2rho)-1)/n  holds at small rho.
#
# RESULT (exact, char-0 prize prime p~n^4, VALID subgroup p=1 mod n, validated vs Rust engine):
#   n=16,k=2: s*=5, s*-k=3, delta*=0.6875  -- formula predicts s*-k = n/4-1 = 3   => MATCH
#   n=32,k=2: s*=6, s*-k=4, delta*=0.8125  -- formula predicts s*-k = n/4-1 = 7   => BREAK
# The in-tree formula (calibrated at rho=1/4, n<=24) OVER-predicts s* (under-predicts delta*)
# at small rho: at n=32,k=2 it says s*=9 (delta*=0.7188) but EXACT is s*=6 (delta*=0.8125),
# ABOVE Johnson(0.75), toward cap 1-rho. s*-k grows 3->4 (NOT 3->7): far SLOWER than the
# formula's n/4 rate. This is the orchestrator's flagged "n=32,k=2 break" pinned exactly.
# Run: python3 probe_407_k2_sstar_formula_break.py <n> [bmax]. Cross-checked against rust-pg bmax mode.

import itertools, sys
from sympy import isprime, primitive_root

def big_prime(n):
    p = n**4
    while True:
        if p % n == 1 and isprime(p): return p
        p += 1

def setup(n):
    p = big_prime(n)
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mu = [pow(h, i, p) for i in range(n)]
    return p, mu

def divdiff(vals, nodes, p):
    # k-th divided difference over len(nodes)=k+1 points
    v = list(vals); m = len(v)
    for j in range(1, m):
        for i in range(m-1, j-1, -1):
            inv = pow((nodes[i]-nodes[i-j]) % p, p-2, p)
            v[i] = ((v[i]-v[i-1]) * inv) % p
    return v[-1]

def in_rs(vals, nodes, k, p):
    s = len(nodes)
    if s <= k: return True
    for st in range(s-k):
        if divdiff(vals[st:st+k+1], nodes[st:st+k+1], p) != 0: return False
    return True

def incidence(mu, a, b, n, k, p, s):
    mua = [pow(x, a, p) for x in mu]
    mub = [pow(x, b, p) for x in mu]
    gammas = set()
    for comb in itertools.combinations(range(n), s):
        nodes = [mu[i] for i in comb]
        u1 = [mub[i] for i in comb]
        if in_rs(u1, nodes, k, p):
            u0 = [mua[i] for i in comb]
            if in_rs(u0, nodes, k, p): return None  # heavy/saturated
            continue
        u0 = [mua[i] for i in comb]
        a0 = divdiff(u0[:k+1], nodes[:k+1], p)
        a1 = divdiff(u1[:k+1], nodes[:k+1], p)
        if a1 == 0: continue
        gm = ((-a0) * pow(a1, p-2, p)) % p
        full = [(u0[i] + gm*u1[i]) % p for i in range(s)]
        if in_rs(full, nodes, k, p): gammas.add(gm)
    return len(gammas)

def maxI_neighborhood(mu, n, k, p, s, bmax=6):
    # extremal dir search: b in [k, k+bmax], a in [k, n)  (max always at small b)
    best = -1; arg=None
    for b in range(k, min(k+bmax, s)):
        for a in range(k, n):
            if a==b: continue
            inc = incidence(mu, a, b, n, k, p, s)
            if inc is None: continue
            if inc > best: best, arg = inc, (a,b)
    return best, arg

if __name__ == "__main__":
    n = int(sys.argv[1]); k = 2; bmax = int(sys.argv[2]) if len(sys.argv)>2 else 6
    p, mu = setup(n)
    budget = n
    print(f"n={n} k={k} p={p} budget={budget} (extremal-nbhd b<=k+{bmax})")
    sstar = None
    for s in range(k+2, n//2+2):
        from math import comb as C
        if C(n,s) > 60_000_000:
            print(f"  s={s} C={C(n,s)} too big, stop"); break
        mx, arg = maxI_neighborhood(mu, n, k, p, s, bmax)
        good = mx <= budget
        print(f"  s={s} (s-k={s-k}): maxI={mx} at {arg}  {'GOOD' if good else 'bad'}")
        if good and sstar is None:
            sstar = s
            print(f"  => s*={s}, s*-k={s-k}, delta*={(n-s)/n:.4f}")
            break

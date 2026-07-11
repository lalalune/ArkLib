#!/usr/bin/env python3
"""
Is the UNION of gamma-aligned a-sets itself gamma-aligned?  (crux of the exact-multiplicity
characterization for issue #444 census face).

A set S is gamma-aligned iff every (k+1)-tuple t in S has residual_u0(t)+gamma*residual_u1(t)=0.
If S1, S2 are both gamma-aligned, is S1 union S2 gamma-aligned?  Risk: a (k+1)-tuple SPANNING
both (some points in S1\\S2, some in S2\\S1) need not lie on the gamma-fibre.

This decides whether the intrinsic "maximal gamma-aligned set" (union of all gamma-aligned sets)
is itself gamma-aligned -- which the Lean brick needs.  We test on the REAL prize structure with
PLANTED multi-block alignment: two overlapping deep sets sharing >= k points, both gamma*-aligned,
and check whether spanning tuples align.
"""
import itertools, random

def is_prime(m):
    if m < 2: return False
    for q in range(2, int(m**0.5)+1):
        if m % q == 0: return False
    return True

def find_prime(n, lo):
    p = lo - (lo % n) + 1
    while p < lo or not is_prime(p):
        p += n
    return p

def primitive_root(p):
    fac = []; m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac):
            return g

def divided_diff_k(xpts, ypts, p):
    k = len(xpts)-1
    y = list(ypts)
    for j in range(1, k+1):
        ny = []
        for i in range(len(y)-1):
            dx = (xpts[i+j]-xpts[i]) % p
            ny.append(((y[i+1]-y[i]) * pow(dx, p-2, p)) % p)
        y = ny
    return y[0] % p

def run(n, p, k, seed):
    rng = random.Random(seed)
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    dom = [pow(h, i, p) for i in range(n)]
    def poly_eval(c, x):
        v = 0
        for cc in reversed(c): v = (v*x+cc) % p
        return v
    gamma = rng.randrange(1, p)
    # Two overlapping blocks B1, B2 both forced onto the gamma-fibre, sharing k points.
    pts = rng.sample(range(n), min(n, k + 6))
    half = (len(pts)+k)//2
    B1 = pts[:half]; B2 = pts[half-k:]   # overlap = k points
    u0 = [rng.randrange(p) for _ in range(n)]
    u1 = [rng.randrange(p) for _ in range(n)]
    ck = [rng.randrange(p) for _ in range(k)]
    for i in set(B1)|set(B2):
        x = dom[i]
        u1[i] = rng.randrange(p)
        u0[i] = (-gamma*u1[i] + poly_eval(ck, x)) % p
    def resid(t, u):
        return divided_diff_k([dom[i] for i in t], [u[i] for i in t], p)
    def aligned(S):
        for t in itertools.combinations(sorted(S), k+1):
            if (resid(t,u0) + gamma*resid(t,u1)) % p != 0:
                return False
        return True
    U = sorted(set(B1)|set(B2))
    # the planted union: is it aligned? find spanning tuples that break it
    nbreak = 0; ntotal = 0
    for t in itertools.combinations(U, k+1):
        ntotal += 1
        if (resid(t,u0)+gamma*resid(t,u1)) % p != 0:
            nbreak += 1
    return len(B1), len(B2), len(U), aligned(B1), aligned(B2), aligned(U), nbreak, ntotal

if __name__ == "__main__":
    print("Is the UNION of gamma-aligned sets gamma-aligned? (prize structure, planted overlap)\n")
    any_break = False
    for (n,k) in [(12,1),(12,2),(16,1),(16,2),(20,2),(16,3)]:
        p = find_prime(n, n**3)
        for seed in range(4):
            b1,b2,u,a1,a2,au,nb,nt = run(n,p,k,seed)
            if nb: any_break = True
            print(f"n={n} k={k} p={p} s={seed}: |B1|={b1} |B2|={b2} |union|={u}  "
                  f"B1aligned={a1} B2aligned={a2} UNIONaligned={au}  spanning-breaks={nb}/{nt}")
    print()
    print("VERDICT: union-of-aligned is", "NOT always aligned (spanning tuples break it)"
          if any_break else "ALWAYS aligned in tests (no spanning break)")

#!/usr/bin/env python3
"""Probe for SubplaneSupplyFloor.lean (#389): the sheared-subplane word.

K a subfield of F with |K| = r, lambda in F minus K.  Domain D = {a + lambda*b : a,b in K}
(n = r^2 distinct points), word w(a + lambda*b) = b.  Claims verified exhaustively:
  (1) exactly r(r+1) lines y = c*x + d agree with w on exactly r points,
  (2) every other line agrees on <= 1 point (histogram is {0, 1, r} only),
  (3) hence per-word explainable-core supply at band m is exactly r(r+1)*C(r, m+3),
      superpolynomial in n = r^2 at every band — with q/n = r^(e-2) unbounded.
Instances: F9/K=F3 (n=q), F27/K=F3 (q >> n), F16/K=F4.
"""
import itertools, collections

def gf(p, e, modpoly):
    els = list(itertools.product(range(p), repeat=e))
    def add(u, v): return tuple((a + b) % p for a, b in zip(u, v))
    def mul(u, v):
        prod = [0] * (2 * e - 1)
        for i, a in enumerate(u):
            for j, b in enumerate(v): prod[i + j] = (prod[i + j] + a * b) % p
        for i in range(2 * e - 2, e - 1, -1):
            c = prod[i]
            if c:
                for j in range(e + 1):
                    prod[i - e + j] = (prod[i - e + j] - c * modpoly[j]) % p
        return tuple(prod[:e])
    one = tuple([1] + [0] * (e - 1))
    return els, add, mul, one

def run(p, e, modpoly, r):
    els, add, mul, one = gf(p, e, modpoly)
    def pw(u, k):
        res = one; b = u
        while k:
            if k & 1: res = mul(res, b)
            b = mul(b, b); k >>= 1
        return res
    K = [x for x in els if pw(x, r) == x]
    assert len(K) == r, (len(K), r)
    lam = next(x for x in els if x not in K)
    D = {}
    for a in K:
        for b in K:
            x = add(a, mul(lam, b))
            assert x not in D, "shear not injective"
            D[x] = b
    n = len(D); assert n == r * r
    hist = collections.Counter()
    rich = 0
    for c in els:
        for d in els:
            ag = sum(1 for x, wx in D.items() if add(mul(c, x), d) == wx)
            hist[ag] += 1
            if ag >= r: rich += 1
    assert rich == r * (r + 1), (rich, r * (r + 1))
    assert all(k in (0, 1, r) for k in hist), dict(hist)
    print(f"F_{p}^{e} (q={p**e}), K=F_{r}, n={n}: rich lines = {rich} = r(r+1); "
          f"histogram {{0,1,r}} only: OK")

if __name__ == "__main__":
    run(3, 2, [1, 0, 1], 3)        # F9,  K=F3: the n = q case
    run(3, 3, [1, 2, 0, 1], 3)     # F27, K=F3: q >> n
    run(2, 4, [1, 1, 0, 0, 1], 4)  # F16, K=F4: char 2
    print("all subplane supply-floor probe checks PASS")

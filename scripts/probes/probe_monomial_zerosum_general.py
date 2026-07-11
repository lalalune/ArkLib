#!/usr/bin/env python3
"""Pre-registered probe (#389): the GENERAL monomial zero-sum identity.

Claim (Vieta): for the word w = x^(k+1), dimension k, agreement >= k+1, on ANY domain,
    list size = #{(k+1)-subsets T of dom : sum(T) = 0}.
Because a deg-<k codeword P agrees with x^(k+1) exactly at the roots of X^(k+1) - P,
a monic degree-(k+1) polynomial whose X^k coefficient is 0 (P has no X^k term), so by
Vieta the (k+1) roots sum to 0; conversely any zero-sum (k+1)-subset gives
P = X^(k+1) - prod(X - x_i) of degree <= k-1.

The cubic (k=2) is the landed CubicOrchardIdentity. This confirms k=2,3,4 before
formalizing the general statement `monomial_list_eq_zeroSum`.
"""
import itertools

def factor(m):
    fs, d = [], 2
    while d * d <= m:
        while m % d == 0:
            fs.append(d); m //= d
        d += 1
    if m > 1: fs.append(m)
    return fs

def primitive_root(q):
    fs = set(factor(q - 1))
    return next(g for g in range(2, q) if all(pow(g, (q-1)//p, q) != 1 for p in fs))

def subgroup(q, n):
    g = primitive_root(q); w = pow(g, (q-1)//n, q)
    return sorted(pow(w, i, q) for i in range(n))

def poly_eval(coeffs, x, q):
    # coeffs low->high
    r = 0
    for c in reversed(coeffs):
        r = (r * x + c) % q
    return r

def list_size_monomial(q, dom, k, a):
    """list size of w = x^(k+1) at dim k (deg<k polys), agreement >= a, by interpolation."""
    n = len(dom)
    w = [pow(x, k + 1, q) for x in dom]
    seen = set()
    cnt = 0
    # a deg<k poly is determined by k points; interpolate through every k-subset
    for idx in itertools.combinations(range(n), k):
        xs = [dom[i] for i in idx]; ys = [w[i] for i in idx]
        # Lagrange interpolation -> coefficient tuple (as a hashable signature via evaluations)
        # represent poly by its values on ALL dom points
        vals = []
        for xq in dom:
            # Lagrange eval at xq
            acc = 0
            for j in range(k):
                num = ys[j]; den = 1
                for l in range(k):
                    if l == j: continue
                    num = num * ((xq - xs[l]) % q) % q
                    den = den * ((xs[j] - xs[l]) % q) % q
                acc = (acc + num * pow(den, q - 2, q)) % q
            vals.append(acc)
        sig = tuple(vals)
        if sig in seen: continue
        seen.add(sig)
        agr = sum(1 for t in range(n) if vals[t] == w[t])
        if agr >= a:
            cnt += 1
    return cnt

def zerosum_subsets(q, dom, r):
    return sum(1 for T in itertools.combinations(dom, r) if sum(T) % q == 0)

if __name__ == "__main__":
    cases = [
        (2, [(29, 14), (31, 15), (37, 18)]),
        (3, [(29, 14), (31, 15), (41, 20)]),
        (4, [(31, 15), (41, 20)]),
    ]
    for k, insts in cases:
        for q, n in insts:
            dom = subgroup(q, n)
            ls = list_size_monomial(q, dom, k, k + 1)
            zs = zerosum_subsets(q, dom, k + 1)
            print(f"k={k} (w=x^{k+1}) q={q} n={n}: list={ls} zero-sum-{k+1}-subsets={zs} "
                  f"{'OK' if ls == zs else 'FAIL'}")

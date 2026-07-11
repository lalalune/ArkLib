#!/usr/bin/env python3
"""Falsify-first probe for the de Bruijn -> MixedRadixTower wiring (#232, O95).

Target Lean statements (field surface, T <= mu_n, n = 2^a * 3^b):
  A (dichotomy): sum(T) = 0  ==>  every y in T has its FULL mu_2-coset or its
     FULL mu_3-coset inside T  (pointwise OR — the sharp t=1 tower layer).
  B (cardinality / Lam–Leung two-prime): sum(T) = 0 ==> |T| in 2N + 3N.
  NEG control 1: vanishing does NOT imply uniform mu_2-closure (rotated mu_3
     packet) — the wall keeping hBase(w=2) conditional.
  NEG control 2: dichotomy does NOT imply vanishing (the corollary is one-way,
     not an iff) — distinguishes statement A from an over-claim.
Exact arithmetic in Z[x]/Phi_n.  Exhaustive n = 12, 18; full MITM census n = 36.
Exit 0 iff all checks pass.
"""
import sys
from itertools import product

def cyclotomic(n):
    # polynomial of x^n - 1 divided by prod of cyclotomic d|n, d<n (recursive, exact)
    import functools
    @functools.lru_cache(None)
    def phi(m):
        # returns tuple of coeffs (low->high)
        num = [0]*(m) + [1]; num[0] = -1  # x^m - 1
        den = [1]
        for d in range(1, m):
            if m % d == 0:
                den = polymul(den, phi(d))
        q, r = polydiv(num, den)
        assert all(c == 0 for c in r), (m, r)
        return tuple(q)
    def polymul(a, b):
        out = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i+j] += x*y
        return out
    def polydiv(a, b):
        a = list(a); q = [0]*(len(a)-len(b)+1)
        for i in range(len(q)-1, -1, -1):
            c = a[i+len(b)-1] // b[-1]
            q[i] = c
            if c:
                for j, y in enumerate(b):
                    a[i+j] -= c*y
        return q, a
    return list(phi(n))

def root_powers(n):
    """x^e mod Phi_n for e < n, as integer tuples of length deg."""
    Phi = cyclotomic(n)
    deg = len(Phi) - 1
    pows = []
    cur = [0]*deg; cur[0] = 1
    for _ in range(n):
        pows.append(tuple(cur))
        nxt = [0]*(deg+1)
        for i, c in enumerate(cur):
            nxt[i+1] = c
        # reduce degree-deg term
        top = nxt[deg]
        red = [nxt[i] - top*Phi[i] for i in range(deg)]
        cur = red
    return pows, deg

def run_level(n, p=2, q=3, mitm=False):
    pows, deg = root_powers(n)
    cos_p = [sum(1 << ((e + t*(n//p)) % n) for t in range(p)) for e in range(n)]
    cos_q = [sum(1 << ((e + t*(n//q)) % n) for t in range(q)) for e in range(n)]
    card_ok = lambda c: any(c == i*p + j*q for i in range(c//p+1) for j in range(c//q+1))

    def dichotomy(mask):
        m = mask
        while m:
            e = (m & -m).bit_length() - 1
            m &= m - 1
            if (mask & cos_p[e]) != cos_p[e] and (mask & cos_q[e]) != cos_q[e]:
                return False
        return True

    def mu_closed(mask, cos):
        m = mask
        while m:
            e = (m & -m).bit_length() - 1
            m &= m - 1
            if (mask & cos[e]) != cos[e]:
                return False
        return True

    vanishing = []
    if not mitm:
        for mask in range(1 << n):
            s = [0]*deg
            m = mask
            while m:
                e = (m & -m).bit_length() - 1
                m &= m - 1
                pe = pows[e]
                for i in range(deg):
                    s[i] += pe[i]
            if all(c == 0 for c in s):
                vanishing.append(mask)
    else:
        h = n // 2
        left = {}
        for mask in range(1 << h):
            s = [0]*deg
            m = mask
            while m:
                e = (m & -m).bit_length() - 1
                m &= m - 1
                pe = pows[e]
                for i in range(deg):
                    s[i] += pe[i]
            left.setdefault(tuple(s), []).append(mask)
        for mask in range(1 << (n - h)):
            s = [0]*deg
            m = mask
            while m:
                e = (m & -m).bit_length() - 1
                m &= m - 1
                pe = pows[h + e]
                for i in range(deg):
                    s[i] += pe[i]
            key = tuple(-c for c in s)
            for lm in left.get(key, ()):
                vanishing.append(lm | (mask << h))

    n_vanish = len(vanishing)
    dich_fail = [m for m in vanishing if not dichotomy(m)]
    card_fail = [m for m in vanishing if not card_ok(bin(m).count('1'))]
    not_mu_p_closed = sum(1 for m in vanishing if m and not mu_closed(m, cos_p))
    not_mu_q_closed = sum(1 for m in vanishing if m and not mu_closed(m, cos_q))
    # NEG control 2 only exhaustive levels: dichotomy sets that do NOT vanish
    dich_not_vanish = None
    if not mitm:
        vs = set(vanishing)
        dich_not_vanish = sum(1 for mask in range(1 << n)
                              if dichotomy(mask) and mask not in vs)
    print(f"n={n}: vanishing={n_vanish} dichotomy_fail={len(dich_fail)} "
          f"card_fail={len(card_fail)} not_mu{p}closed={not_mu_p_closed} "
          f"not_mu{q}closed={not_mu_q_closed} dich_not_vanish={dich_not_vanish}")
    ok = (len(dich_fail) == 0 and len(card_fail) == 0
          and not_mu_p_closed > 0          # NEG control 1: uniform closure FALSE
          and (mitm or dich_not_vanish > 0))  # NEG control 2: one-way corollary
    return ok, n_vanish

def main():
    ok12, v12 = run_level(12)
    ok18, v18 = run_level(18)
    ok36, v36 = run_level(36, mitm=True)
    # census cross-checks against O94/O70/O67 recorded counts
    census = (v12 == 100 and v18 == 1000)
    print(f"census cross-check (n=12:100, n=18:1000): {census}; n=36 count={v36}")
    if ok12 and ok18 and ok36 and census:
        print("ALL CHECKS PASS")
        return 0
    print("FAILURE")
    return 1

if __name__ == "__main__":
    sys.exit(main())

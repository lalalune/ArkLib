#!/usr/bin/env python3
"""
A10 NEAR-CAPACITY BLOWUP -- pin the transition radius delta*(n,rho) EXACTLY.

The exact far-line incidence object (from probe_farline_incidence_exact.py, axiom-clean in-tree):
  I(a,b; r) = #{ gamma in F_p : x^a + gamma*x^b agrees with SOME RS[mu_n,k] codeword on >= n-r pts }.
  delta* = sup{ delta : max_FAR_dir I(a,b; floor(delta n)) <= budget }, budget = n (prize q*eps*~n).

A10 task: trace max-far-incidence MFI(r) as r grows. It is O(n) (typically 1 single coset of
gammas) up to a cliff radius r*, then BLOWS UP (R4: 219-coset blowup near capacity). The cliff is
delta* = (r*-1)/n.  Characterize r*(n,rho) exactly.

This probe:
  (1) traces the full MFI(r) curve for each (n,k) -- shows the cliff,
  (2) records r* = first r with MFI > budget; delta* = (r*-1)/n,
  (3) records the BINDING direction (a,b) at the cliff,
  (4) p-independence check on >=2 big primes q (over-det band proven p-independent).

Faithful: mu_n PROPER subgroup (n=2^a), big prime q ~ n^4, p % n == 1.  Char-0 combinatorial.
DO NOT git commit (orchestrator handles it).
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c

def find_prime(n, lo):
    """big prime q>lo, q%n==1, v2(q-1)==v2(n) (faithful: no extra 2-torsion, no Fermat)."""
    vn = v2(n)
    q = ((lo // n) + 1) * n + 1
    while True:
        if q > lo and (q - 1) % n == 0 and v2(q - 1) == vn and isprime(q): return q
        q += n

def subgroup(p, n):
    # find generator of mu_n
    e = (p - 1) // n
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        # check order exactly n
        ok = True
        x = h
        for j in range(1, n):
            if x == 1: ok = False; break
            x = x * h % p
        if ok and x == 1:
            S = []; y = 1
            for _ in range(n): y = y * h % p; S.append(y)
            if len(set(S)) == n: return sorted(S)
    raise RuntimeError("no subgroup")

def left_null_basis(rows, p):
    """left null space of the (m x k) matrix `rows` over F_p: vectors v with v*rows = 0."""
    m = len(rows); k = len(rows[0]) if m else 0
    aug = [rows[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    # rref
    pr = 0
    for c in range(k):
        sel = next((r for r in range(pr, m) if aug[r][c] % p), None)
        if sel is None: continue
        aug[pr], aug[sel] = aug[sel], aug[pr]
        inv = pow(aug[pr][c], p - 2, p)
        aug[pr] = [(x * inv) % p for x in aug[pr]]
        for r in range(m):
            if r != pr and aug[r][c] % p:
                f = aug[r][c]; aug[r] = [(aug[r][j] - f * aug[pr][j]) % p for j in range(k + m)]
        pr += 1
        if pr == m: break
    return [[row[k + j] % p for j in range(m)] for row in aug
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence(S, p, k, a, b, r):
    """exact I(a,b;r): (#gammas, saturated)."""
    n = len(S); size = n - r
    if size <= k: return p, True
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null_basis(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): return p, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return len(good), False

def max_far_incidence(S, p, k, r):
    """max over FAR monomial dirs (b in [k, n-r)) of I(a,b;r); returns (max, binder)."""
    n = len(S); size = n - r; best = (-1, None)
    for b in range(k, size):
        for a in range(n):
            if a == b: continue
            c, sat = incidence(S, p, k, a, b, r)
            if c > best[0]: best = (c, (a, b))
    return best

def trace(n, k, p, budget):
    """full MFI(r) curve; returns (rows, r_star). r_star = first r with MFI>budget."""
    rows = []; r_star = None
    for r in range(k + 1, n - k + 1):
        size = n - r
        if size <= k: break
        mx, binder = max_far_incidence(S, p, k, r)
        cap = (mx >= p)
        rows.append((r, size, mx, binder, cap))
        if (mx > budget or cap) and r_star is None:
            r_star = r
    return rows, r_star

if __name__ == '__main__':
    # 2-power subgroups (faithful), rho in {1/4, 1/2}.
    cases = [(8, 2), (8, 4), (16, 4), (16, 8)]
    for (n, k) in cases:
        rho = k / n; budget = n
        for p in (find_prime(n, n**4), find_prime(n, 3 * n**4 + 100)):
            S = subgroup(p, n)
            rows, r_star = trace(n, k, p, budget)
            ds = (r_star - 1) / n if r_star else None
            print(f"\nn={n} k={k} rho={rho:.3f} p={p} (q/n^4={p/n**4:.1f}) budget={budget}")
            print(f"  r : size : MFI : binder(a,b) : cap?")
            for (r, size, mx, binder, cap) in rows:
                flag = " <<< CLIFF" if r == r_star else ""
                capf = " SAT" if cap else ""
                print(f"  {r:2d} : {size:3d} : {mx:5d} : {binder}{capf}{flag}")
            print(f"  => r*={r_star}  delta*={ds}  (capacity 1-rho={1-rho:.4f}, johnson={1-(rho**0.5):.4f})")

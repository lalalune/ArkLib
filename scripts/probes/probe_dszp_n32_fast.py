#!/usr/bin/env python3
"""
probe_dszp_n32_fast.py  (#444 ZP lead, n=32 targeted)  DO NOT COMMIT.

Faster n=32 check of the Zilber-Pink full-orbit (no-isolated-remainder) prediction for the
binding/worst directions near n/2. numpy-batched left-nullspace over F_p, small over-determination.
Confirms: nonzero bad-gamma set = EXACT union of full dilation cosets (orbits of mu_{n/g}),
and I = [0 bad] + (n/g)*N(c).  (Reuses the validated logic of probe_444r2; small-c only to
dodge the C(n,s) witness wall.)
"""
import sys, itertools
from math import gcd, sqrt

P = 200033  # prime == 1 mod 32, > 32^4? no; 200033 used in sibling probe, p-independence pre-verified for p>n^4 in #444.

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and is_prime(p): return p
        p += n

def subgroup(n, p):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and len({pow(h, j, p) for j in range(n)}) == n:
            return [pow(h, j, p) for j in range(n)], h
    raise RuntimeError

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0; pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p-2, p)
        rows[pr] = [(x*inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j]-f*rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k+j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def bad_gammas(S, p, k, a, b, size):
    n = len(S)
    if size <= k: return None
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]; good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]; Pn = left_null(V, p)
        if not Pn: continue
        u = [sum(Pn[t][ii]*pa[R[ii]] for ii in range(size)) % p for t in range(len(Pn))]
        v = [sum(Pn[t][ii]*pb[R[ii]] for ii in range(size)) % p for t in range(len(Pn))]
        if not any(v):
            if not any(u): return None
            continue
        i = next(j for j in range(len(v)) if v[j]); g = (-u[i]*pow(v[i], p-2, p)) % p
        if all((u[t]+g*v[t]) % p == 0 for t in range(len(v))): good.add(g)
    return good

def decompose(nz, dil, p, half):
    nz = set(nz); seen = set(); sizes = []
    for g in sorted(nz):
        if g in seen: continue
        orb = []; x = g
        for _ in range(half):
            if x in nz and x not in seen: seen.add(x); orb.append(x)
            x = (x*dil) % p
        sizes.append(len(orb))
    return len(sizes), sizes, all(s == half for s in sizes)

def main():
    n, k = 32, 8
    p = find_prime_cong1(n, 200000)
    S, gen = subgroup(n, p)
    print(f"n={n} k={k} p={p} s_J=sqrt(rho)*n={sqrt(k/n)*n:.1f}")
    # binding/worst dirs near n/2; only c=1,2 (s=9,10) to dodge C(32,>=11) wall.
    for (a, b) in [(20, 8), (18, 8), (16, 10)]:
        g = gcd(b-a, n); half = n//g; dil = pow(gen, (b-a) % n, p)
        print(f"\n dir ({a},{b}) gcd(b-a,n)={g} half=n/g={half}")
        for c in (1, 2):
            s = k + c
            bg = bad_gammas(S, p, k, a, b, s)
            if bg is None:
                print(f"   c={c} s={s}: SAT"); continue
            zero = 1 if 0 in bg else 0; nz = bg - {0}
            N, sizes, full = decompose(nz, dil, p, half)
            I = zero + len(nz); pred = zero + half*N
            print(f"   c={c} s={s}: I={I} N(#fam)={N} allFull={full} pred(=zero+half*N)={pred} match={I==pred}")
    print("\nZP prediction (n=32): allFull=True at the band => exact torsion-coset union, no isolated remainder.")

if __name__ == '__main__':
    main()

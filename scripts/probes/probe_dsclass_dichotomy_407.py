#!/usr/bin/env python3
"""#407 dichotomy CLASSIFIER cross-check (DO NOT COMMIT). Confirms the over/under-determination rigidity:
   - UNDER-det (1 condition): bad-prime / faithfulness threshold GROWS with n -> BGK wall.
   - OVER-det (>=2 simultaneous conditions): bad-prime threshold stays ~poly(n) (~n^2) and vanishes deep.
Three test objects:
  (A) single subset-sum coincidence Sum_{s in S} zeta^s ≡ 0 mod p  [additive-energy / E_r core, r=1, UNDER-det]
  (B) full simultaneous odd system e_1=e_3=...=0 (r=k/2 conds)       [higher-order-MDS / Q1 core, OVER-det]
  (C) generalized-Vandermonde / Schur minor det ≡ 0 mod p           [NVM, multi-minor, OVER-det]
For each we report the largest prime p≡1 mod n that admits a SPURIOUS char-p solution with NO char-0
solution. Under-det: max-bad grows superlinearly. Over-det: max-bad ~ n^2, capped well below."""
import itertools

def isp(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primes_1modn(n, lo, hi):
    return [p for p in range(max(lo, n+1), hi) if p % n == 1 and isp(p)]

def proot_order_n(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and (n == 1 or pow(h, n//2, p) != 1):
            return h
    return None

# ---------- (A) single subset-sum: Sum_{i in S} zeta^i ≡ 0 (UNDER-det, r=1) ----------
# char-0: a non-antipodal S has Sum != 0 (no vanishing without antipodal pairs, for small S vs phi(n)).
# We test S of fixed size t, NON-antipodal (no i with i+n/2 also in S). max bad prime = faithfulness threshold.
def underdet_subsetsum(n, t, lo, hi):
    half = n // 2
    maxbad = 0; nbad = 0; scanned = 0
    sets = []
    for S in itertools.combinations(range(n), t):
        Ss = set(S)
        if any((i + half) % n in Ss for i in S):  # skip antipodal-containing (char-0 can vanish)
            continue
        sets.append(S)
    for p in primes_1modn(n, lo, hi):
        z = proot_order_n(p, n)
        if z is None: continue
        zp = [pow(z, i, p) for i in range(n)]
        scanned += 1
        bad = False
        for S in sets:
            if sum(zp[i] for i in S) % p == 0:
                bad = True; break
        if bad:
            maxbad = p; nbad += 1
    return scanned, maxbad, nbad, len(sets)

# ---------- (B) simultaneous odd system (OVER-det, r=k/2) ----------  (same as probe_simultaneous_rigidity)
def overdet_oddsystem(k, r, lo, hi):
    n = 4*k; reps = 2*k; odd = [2*t+1 for t in range(r)]
    EPS = list(itertools.product([1, -1], repeat=reps))
    maxbad = 0; nbad = 0; scanned = 0
    for p in primes_1modn(n, lo, hi):
        z = proot_order_n(p, n)
        if z is None: continue
        zp = [pow(z, t, p) for t in range(n)]
        scanned += 1
        cnt = 0
        for eps in EPS:
            ok = True
            for j in odd:
                if sum(eps[i]*zp[(i*j) % n] for i in range(reps)) % p != 0:
                    ok = False; break
            if ok: cnt += 1
        if cnt > 0:
            maxbad = p; nbad += 1
    return scanned, maxbad, nbad

# ---------- (C) generalized-Vandermonde / Schur minor det ≡ 0 mod p (OVER-det) ----------
# A t x t minor of the Vandermonde-type matrix [zeta^{a_i * c_j}] for distinct exponent rows a_i in mu_n,
# columns c_j a strictly-increasing exponent set (lambda + delta). det = 0 is a SINGLE polynomial condition
# but the Schur/hook-content factorization makes it a PRODUCT of (zeta^{a_i}-zeta^{a_j}) [Vandermonde] times
# Schur poly -> over-determined (many factor conditions). char-0: nonzero (distinct points). max bad prime.
def overdet_genvander(n, t, lo, hi):
    # rows: first t elements of mu_n; cols: exponents (0,1,...,t-2, t)  (one "gap" -> nontrivial Schur)
    cols = list(range(t-1)) + [t]
    maxbad = 0; nbad = 0; scanned = 0
    for p in primes_1modn(n, lo, hi):
        z = proot_order_n(p, n)
        if z is None: continue
        pts = [pow(z, i, p) for i in range(t)]
        M = [[pow(pts[i], c, p) for c in cols] for i in range(t)]
        # det mod p
        det = 1; A = [row[:] for row in M]
        for col in range(t):
            piv = None
            for rrow in range(col, t):
                if A[rrow][col] % p != 0: piv = rrow; break
            if piv is None: det = 0; break
            if piv != col:
                A[col], A[piv] = A[piv], A[col]; det = (-det) % p
            inv = pow(A[col][col], p-2, p); det = det * A[col][col] % p
            for rrow in range(col+1, t):
                f = A[rrow][col] * inv % p
                for cc in range(col, t):
                    A[rrow][cc] = (A[rrow][cc] - f*A[col][cc]) % p
        scanned += 1
        if det % p == 0:
            maxbad = p; nbad += 1
    return scanned, maxbad, nbad

if __name__ == "__main__":
    import sys
    HI = 40000
    print("=== (A) UNDER-det single subset-sum (additive-energy r=1) — threshold should GROW with n ===", flush=True)
    for n, t in [(8, 3), (12, 4), (16, 5), (20, 5)]:
        sc, mb, nb, ns = underdet_subsetsum(n, t, 17, HI); sys.stdout.flush()
        print(f"  n={n:3d} t={t} non-antip-sets={ns:6d}: {sc:4d} primes<{HI}; max bad prime={mb:6d}; #bad={nb}  (bad/n^2={mb/n**2:6.2f}, bad/n^3={mb/n**3:6.3f})", flush=True)
    print("=== (B) OVER-det simultaneous odd system (Q1 / higher-order-MDS) — should cap ~poly(k), vanish deep ===", flush=True)
    for k, r in [(4, 1), (4, 2), (6, 1), (6, 2), (6, 3), (8, 4)]:
        sc, mb, nb = overdet_oddsystem(k, r, 4*k+1, HI)
        n = 4*k
        tag = "UNDER(r=1)" if r == 1 else "OVER"
        print(f"  k={k} n={n} r={r} [{tag:10s}]: {sc:4d} primes<{HI}; max bad prime={mb:7d}; #bad={nb}  ((2k)^(2k/r)={(2*k)**(2*k//r):>10}, n^2={n**2})", flush=True)
    print("=== (C) OVER-det generalized-Vandermonde minor (NVM/Schur) — should cap ~n^2 ===", flush=True)
    for n, t in [(16, 4), (32, 5), (64, 6), (128, 6)]:
        sc, mb, nb = overdet_genvander(n, t, 17, HI)
        print(f"  n={n:4d} t={t}: {sc:4d} primes<{HI}; max bad prime={mb:6d}; #bad={nb}  (ratio bad/n^2={mb/n**2:.3f})", flush=True)

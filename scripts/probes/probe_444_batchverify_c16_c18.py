#!/usr/bin/env python3
"""probe_444_batchverify_c16_c18.py  (#444 BATCH-VERIFY: C16 Lenstra coset-core, C18 Bi-Cheng-Gao sparse-root)

Both C16 and C18 claim the FAR-LINE agreement set S = {x in mu_n : x^a + g x^b delta-close RS[k]}
decomposes as (coset core) U (small ragged residue), and that the binding object reaches PAST
Johnson. We test the two horns with the EXACT far-line incidence / max-zero engine, proper mu_n,
p PRIME, p >> n^3, p == 1 mod n, index (p-1)/n >= 2, NEVER n=p-1, multi-prime char-faithfulness.

HORN 1 (C16): "coset core capped below n/2" — does the largest mu_d-coset-union inside the BINDING
              witness reach n/2? If it reaches n/2 the cap is false; if the GENUINE binding object
              (subgroup-saturation excluded) is sub-Johnson, C16 reduces to Johnson.
HORN 2 (C18): "sparse-root coset core DOMINATES, residue small" — is the binding witness actually a
              union of small-subgroup cosets, and does its size exceed Johnson sqrt(kn)?

Engine: every minimal-support codeword of the (k+2)-spectral code vanishes on K-1 generic coords;
we enumerate (K-1)-subsets only for tractable n, and we restrict to FAR directions gcd(a-b,n)>=2.
We dump the binding witness, its coset-core size, and whether it is subgroup-saturated.
"""
import itertools, sys
from math import gcd, isqrt

def out(*a): print(*a); sys.stdout.flush()

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def find_prime(n, beta):
    target = int(round(n**beta)); p = target - (target % n) + 1
    if p <= n+1: p += n
    for _ in range(4000000):
        if (p-1) % n == 0 and (p-1)//n >= 2 and isprime(p): return p
        p += n
    return None

def rou(p, n):
    g = 2
    while g < p:
        h = pow(g, (p-1)//n, p)
        if all(pow(h, d, p) != 1 for d in range(1, n)) and pow(h, n, p) == 1:
            return h
        g += 1
    return None

def solve_null_one(rows, p):
    K = len(rows[0]); R = [r[:] for r in rows]
    pivcols = []; pivrow = 0
    for col in range(K):
        sel = None
        for i in range(pivrow, len(R)):
            if R[i][col] % p != 0: sel = i; break
        if sel is None: continue
        R[pivrow], R[sel] = R[sel], R[pivrow]
        inv = pow(R[pivrow][col], p-2, p)
        R[pivrow] = [(x*inv) % p for x in R[pivrow]]
        for i in range(len(R)):
            if i != pivrow and R[i][col] % p != 0:
                f = R[i][col]; R[i] = [(R[i][j]-f*R[pivrow][j]) % p for j in range(K)]
        pivcols.append(col); pivrow += 1
    free = [c for c in range(K) if c not in pivcols]
    if not free: return None
    fc = free[0]; c = [0]*K; c[fc] = 1
    for ri, pc in enumerate(pivcols):
        c[pc] = (-R[ri][fc]) % p
    return c

def divisors_gt1(n):
    return [d for d in range(2, n+1) if n % d == 0]

def coset_core_size(Z, n):
    Zs = set(Z); best = 0
    for d in divisors_gt1(n):
        step = n // d
        covered = 0
        for r in range(step):
            cls = set((r + j*step) % n for j in range(d))
            if cls <= Zs: covered += d
        best = max(best, covered)
    return best

def has_big_subgroup_coset(Z, n, thresh):
    """True if Z contains a coset of a subgroup of order >= thresh (the saturation degeneracy)."""
    Zs = set(Z)
    for d in divisors_gt1(n):
        if d < thresh: continue
        step = n // d
        for r in range(step):
            cls = set((r + j*step) % n for j in range(d))
            if cls <= Zs: return True
    return False

def maxzeros(n, p, h, k, a, b):
    T = sorted(set((list(range(k)) + [a, b])[i] % n for i in range(k+2)))
    K = len(T)
    if K < 2 or K > n: return None
    rows = [[pow(h, (t*z) % n, p) for t in T] for z in range(n)]
    best_s = -1; best_Z = None
    for sub in itertools.combinations(range(n), K-1):
        c = solve_null_one([rows[i] for i in sub], p)
        if c is None: continue
        Z = [z for z in range(n) if sum(rows[z][j]*c[j] for j in range(K)) % p == 0]
        if len(Z) > best_s:
            best_s = len(Z); best_Z = Z
    return best_s, best_Z

def main():
    out("="*100)
    out("C16 / C18 BATCH-VERIFY: far-line coset-core, two horns, exact, proper mu_n, p>>n^3, p==1(n) index>=2")
    out("="*100)
    # tractable: K-1 = k+1 choose from n. n=8 (k<=3), n=16 (k<=4) are fine; n=32 only k<=3.
    cases = [(8,2,4.0),(8,2,5.0),(8,3,4.0),(16,2,4.0),(16,3,4.0),(16,4,4.5),(32,2,4.0),(32,3,4.0)]
    rows_out = []
    for (n,k,beta) in cases:
        p = find_prime(n, beta); h = rou(p, n) if p else None
        if h is None: out(f"n={n} k={k}: no prime/root"); continue
        johnson = (k*n)**0.5
        best = None
        for a in range(1, n):
            for b in range(0, a):
                d = (a-b) % n or n
                if gcd(d, n) < 2: continue   # FAR direction only
                res = maxzeros(n, p, h, k, a, b)
                if res is None: continue
                s, Z = res
                if best is None or s > best[0]:
                    best = (s, a, b, Z)
        if best is None: out(f"n={n} k={k} p={p}: no far dir"); continue
        s, a, b, Z = best
        core = coset_core_size(Z, n)
        ragged = s - core
        saturated = has_big_subgroup_coset(Z, n, max(2, n//4))
        # genuine s* excluding saturation: re-max only over witnesses w/o big subgroup coset
        genuine = None
        for a2 in range(1, n):
            for b2 in range(0, a2):
                d2 = (a2-b2) % n or n
                if gcd(d2, n) < 2: continue
                res = maxzeros(n, p, h, k, a2, b2)
                if res is None: continue
                s2, Z2 = res
                if not has_big_subgroup_coset(Z2, n, max(2, n//4)):
                    if genuine is None or s2 > genuine[0]:
                        genuine = (s2, a2, b2, Z2)
        gs = genuine[0] if genuine else 0
        out(f"\nn={n:3d} k={k} p={p} (~n^{beta}) idx={(p-1)//n} [p>>n^3:{p>n**3}] [n!=p-1:{p-1!=n}]")
        out(f"  BINDING (a,b)=({a},{b}) gcd={gcd((a-b)%n or n,n)}  s*={s}  Johnson={johnson:.2f}")
        out(f"  coset-core={core}  ragged={ragged} (C16/C18 claim small <= k+1={k+1})")
        out(f"  core>=n/2 ({n//2})? {core>=n//2}   s*>Johnson? {s>johnson}   subgroup-saturated witness? {saturated}")
        out(f"  GENUINE s* (saturation excluded) = {gs}  <= Johnson? {gs<=johnson}  witness={sorted(genuine[3]) if genuine else None}")
        rows_out.append((n,k,s,johnson,core,saturated,gs))
    out("\n" + "="*100)
    out("SUMMARY")
    out(f"  {'n':>3} {'k':>2} {'s*':>3} {'John':>6} {'core':>4} {'sat?':>5} {'genuine_s*':>10} {'genuine<=John?':>14}")
    for (n,k,s,j,core,sat,gs) in rows_out:
        out(f"  {n:>3} {k:>2} {s:>3} {j:>6.2f} {core:>4} {str(sat):>5} {gs:>10} {str(gs<=j):>14}")
    out("\nREAD:")
    out("  C16 'core capped below n/2': if any binding core REACHES n/2 the literal cap is false;")
    out("       if the GENUINE (saturation-excluded) binding s* is <= Johnson, C16 only reaches Johnson.")
    out("  C18 'sparse-root core dominates past Johnson': true only via the subgroup-SATURATED witness,")
    out("       which is the two-layer degeneracy artifact (a=n/2 / even-subgroup). Genuine -> Johnson.")
    out("="*100)

if __name__ == "__main__":
    main()

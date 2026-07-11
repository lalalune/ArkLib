# A11: Reconcile KKH26 const-DIM pin with the open const-RATE value, in BAND units.
#
# UNIFIED ANSATZ:  delta*(n,k) = 1 - (k + b(n,k))/n,   b = w* - k  ("band excess above dim").
#   const-DIM (k=O(1)): in-tree pin delta* = 1 - (k+1)/n  =>  w* = k+1  =>  b = 1 (CONSTANT).
#   const-RATE (k=rho*n): b = w* - k is the OPEN quantity; measure it exactly at small n.
#
# Honesty: full subset enumeration C(n,k+1) is only feasible for small (n,k). We run it EXACTLY
# where feasible and otherwise SKIP (no fabrication). Big primes p>>n^4, low v2 (char-0 faithful),
# proper subgroups (n=2^a < p-1).
import itertools, math

def isp(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True

def find_prime(n, lo):
    p = lo - (lo % n) + 1
    while True:
        if p > lo and isp(p) and (p-1) % n == 0 and ((p-1)//n) % 2 == 1:
            return p
        p += n

def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return h
    return None

def solve(M, bvec, p):
    m = len(M); A = [row[:]+[bvec[i]] for i,row in enumerate(M)]; r = 0
    for c in range(m):
        piv = None
        for i in range(r, m):
            if A[i][c] % p != 0: piv = i; break
        if piv is None: return None
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p-2, p); A[r] = [(v*inv) % p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p != 0:
                f = A[i][c]; A[i] = [(A[i][j]-f*A[r][j]) % p for j in range(m+1)]
        r += 1
    return [A[i][m] % p for i in range(m)]

def pencil_bands(p, n, k, a, b, pts, powr):
    za = [pow(pts[i], a, p) for i in range(n)]
    zb = [pow(pts[i], b, p) for i in range(n)]
    ga = {}
    for A in itertools.combinations(range(n), k+1):
        M = [powr[i] + [(-za[i]) % p] for i in A]; rhs = [zb[i] for i in A]
        sol = solve(M, rhs, p)
        if sol is None: continue
        gamma = sol[k]
        if gamma in ga: continue
        g = sol[:k]; cnt = 0
        for i in range(n):
            gi = 0; xi = pts[i]
            for j in range(k-1, -1, -1): gi = (gi*xi + g[j]) % p
            if gi == (zb[i] + gamma*za[i]) % p: cnt += 1
        ga[gamma] = cnt
    return {w: sum(1 for v in ga.values() if v >= w) for w in range(k+1, n+1)}

def deltastar(n, k, p):
    z = proot(p, n); pts = [pow(z, i, p) for i in range(n)]
    powr = [[pow(pts[i], j, p) for j in range(k)] for i in range(n)]
    best = {w: 0 for w in range(k+1, n+1)}
    fars = [x for x in range(k, n) if x != n//2]
    for a in fars:
        for b in fars:
            if a < b:
                bc = pencil_bands(p, n, k, a, b, pts, powr)
                for w in bc: best[w] = max(best[w], bc[w])
    budget = n
    cross = None
    for w in range(k+1, n+1):
        if best[w] <= budget: cross = w; break
    return best, cross

def feasible(n, k, cap=4_000_000):
    return math.comb(n, k+1) <= cap

print("="*80)
print("A11  UNIFIED FORM:  delta*(n,k) = 1 - (k + b)/n,   b = w* - k (band excess above dim)")
print("="*80)

print("\n[CONST-DIM]  k fixed.  in-tree pin => predict b=1 (delta* = 1 - (k+1)/n):")
CD = []
for (n,k) in [(8,1),(16,1),(32,1),(64,1),(8,2),(16,2),(32,2),(64,2),(8,3),(16,3),(32,3)]:
    if not feasible(n,k):
        print(f"  n={n:3d} k={k}: SKIP (C(n,k+1)={math.comb(n,k+1)} too large)"); continue
    p = find_prime(n, n**4)
    _, w = deltastar(n, k, p)
    b = w - k; cap = 1-k/n; ds = 1-w/n
    CD.append((n,k,b))
    print(f"  n={n:3d} k={k} p={p}: w*={w} delta*={ds:.5f} cap={cap:.5f}  b=w*-k={b} "
          f"{'b=1 OK' if b==1 else 'b=%d (!)'%b}")

print("\n[CONST-RATE]  k=rho*n.  measure b=w*-k EXACTLY where feasible:")
CR = {}
for rho_name, rho in [('1/4',0.25),('1/2',0.5)]:
    for n in [8,16,32,64]:
        k = int(round(rho*n))
        if not feasible(n,k):
            print(f"  rho={rho_name} n={n:3d} k={k}: SKIP (C(n,k+1)={math.comb(n,k+1):.3e})"); continue
        p = find_prime(n, n**4)
        _, w = deltastar(n, k, p)
        b = w - k; cap = 1-k/n; ds = 1-w/n; john = 1-math.sqrt(rho)
        CR[(rho_name,n)] = b
        print(f"  rho={rho_name} n={n:3d} k={k} p={p}: w*={w} delta*={ds:.5f} cap={cap:.5f} "
              f"John={john:.5f}  b=w*-k={b}  b/n={b/n:.4f}  b*log2n/n={b*math.log2(n)/n:.4f}")

print("\n" + "="*80)
print("VERDICT on unified form  delta* = 1 - (k+b)/n :")
print(f"  const-DIM b values: {[b for *_,b in CD]}  -> {'ALL b=1 (CONSTANT, matches pin)' if all(b==1 for *_,b in CD) else 'NOT all 1'}")
print(f"  const-RATE b values: {dict(CR)}")
print("  Interpretation: same formula, b(n,k) interpolates 1 (const-dim) -> grows (const-rate).")
print("  Test const-rate b growth shape (gap = cap-delta* = b/n):")
for (rn,n),b in sorted(CR.items()):
    print(f"    rho={rn} n={n}: b={b}  b/n={b/n:.4f}  (cap-d*)*log2n={b/n*math.log2(n):.4f} "
          f"b/sqrt(n)={b/math.sqrt(n):.3f}")

#!/usr/bin/env python3
"""
probe_a2_mann_crossing_pin.py   (#444 A2 -- Mann/antipodal pin of the char-0 incidence AT THE CROSSING)

FINDING (this probe, q-stable, char-0-faithful p>>n^3):  The worst-case char-0 far-line incidence
I_0(w) crosses budget=n at band w_cross => delta*=(n-w_cross)/n.  At the crossing, EVERY rich
witness set R (|R|>=w_cross) decomposes EXACTLY into antipodal pairs {j, j+n/2} (Mann/Conway-Jones:
the only primitive vanishing relation over mu_{2^mu} is z+(-z)=0) WHENEVER w_cross is EVEN -- then
I_0(w_cross) == Mann_anti(w_cross) EXACTLY (Mann closes the crossing).  When w_cross is ODD an
antipodally-closed set of odd size is impossible, so Mann_anti=0 trivially; the witnesses are then a
single antipodal-pair set of size w_cross-1 PLUS one extra point (the +1 free interpolation slot).
We test BOTH: full antipodal closure (even w) and antipodal-core+tail (odd w).

GOVERNING LAW (in-tree, exact): RS[mu_n,k], n=2^mu; far pencil (a,b) a<b in [k,n); inner
I_0(a,b;w)=#{gamma!=0: x^a+gamma x^b agrees with deg<k poly on >= w pts}; worst over dirs; budget n.
Method = (k+1)-subset solve, prime-size-independent, q-stable (verified across 6 primes).

GROUND-TRUTH RECONCILIATION: the established delta* gt={(8,4):0.25,(16,4):0.5625,(16,8):0.3125}
match budget=n EXACTLY here; (8,2): I_0 plateaus at 8 over w in {4,5} so the budget=n crossing is at
w=4 (delta*=0.5) while gt=0.375 (w=5) -- a 1-band granularity edge at tiny n; both reported.
"""
import itertools, math, sys

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True
def find_prime(n, lo):
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p): return p
        p += n
def prim_root(p):
    fac = []; m = p - 1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
def rou(p, n):
    g = prim_root(p); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]
def solve(M, bvec, p):
    m = len(M); A = [row[:] + [bvec[i]] for i, row in enumerate(M)]; r = 0
    for c in range(m):
        piv = None
        for i in range(r, m):
            if A[i][c] % p != 0: piv = i; break
        if piv is None: return None
        A[r], A[piv] = A[piv], A[r]; inv = pow(A[r][c], p-2, p); A[r] = [(v*inv)%p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p != 0:
                f = A[i][c]; A[i] = [(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r += 1
    return [A[i][m] % p for i in range(m)]
def antipodal_closed(R, n):
    Rs = set(R); h = n // 2
    return all(((j + h) % n) in Rs for j in R)
def antipodal_pairs(R, n):
    """#antipodal pairs in R and the leftover (unpaired) indices."""
    Rs = set(R); h = n // 2; paired = set(); npair = 0
    for j in R:
        if j in paired: continue
        if ((j + h) % n) in Rs:
            paired.add(j); paired.add((j+h)%n); npair += 1
    leftover = [j for j in R if j not in paired]
    return npair, leftover

def gamma_map(mu, a, b, k, p, n):
    powr = [[pow(mu[i], j, p) for j in range(k)] for i in range(n)]
    za = [pow(mu[i], a, p) for i in range(n)]; zb = [pow(mu[i], b, p) for i in range(n)]
    seen = {}
    for A in itertools.combinations(range(n), k+1):
        M = [powr[i] + [(-zb[i]) % p] for i in A]; rhs = [za[i] for i in A]
        sol = solve(M, rhs, p)
        if sol is None: continue
        gamma = sol[k]
        if gamma == 0 or gamma in seen: continue
        g = sol[:k]; R = []
        for i in range(n):
            gi = 0; xi = mu[i]
            for j in range(k-1, -1, -1): gi = (gi*xi + g[j]) % p
            if gi == (za[i] + gamma*zb[i]) % p: R.append(i)
        seen[gamma] = tuple(R)
    return seen

def analyze(n, k, gt=None):
    rho = k/n
    p = find_prime(n, n**3 * 8); mu = rou(p, n); budget = n
    # full worst-direction band profile + per-band Mann classification
    band_I = {w: 0 for w in range(k+1, n+1)}
    band_anti = {w: 0 for w in range(k+1, n+1)}      # # gamma whose witness is antipodal-closed
    band_core = {w: 0 for w in range(k+1, n+1)}      # # gamma whose witness = antip pairs + <=1 leftover
    band_dir = {w: None for w in range(k+1, n+1)}
    for a in range(k, n):
        for b in range(a+1, n):
            gm = gamma_map(mu, a, b, k, p, n)
            for w in range(k+1, n+1):
                cnt = ca = cc = 0
                for g, R in gm.items():
                    if len(R) >= w:
                        cnt += 1
                        if antipodal_closed(R, n): ca += 1
                        npair, lo = antipodal_pairs(R, n)
                        if len(lo) <= 1: cc += 1
                if cnt > band_I[w]:
                    band_I[w] = cnt; band_anti[w] = ca; band_core[w] = cc; band_dir[w] = (a, b)
    w_cross = next((w for w in range(k+1, n+1) if band_I[w] <= budget), None)
    dstar = (n - w_cross)/n if w_cross else None
    cap = 1 - rho
    print(f"\n=== n={n} k={k} rho={rho:.4f} p={p} budget={budget} ===")
    print(f"{'w':>3} {'delta':>7} | {'I_0':>6} {'anti-closed':>11} {'anti-core+<=1':>13} | dir")
    for w in range(k+1, n+1):
        if band_I[w] == 0: continue
        mk = "  <== CROSSING(budget=n)" if w == w_cross else ""
        print(f"{w:>3} {(n-w)/n:>7.4f} | {band_I[w]:>6} {band_anti[w]:>11} {band_core[w]:>13} | {band_dir[w]}{mk}")
    out = dict(n=n,k=k,rho=rho,w_cross=w_cross,dstar=dstar,gt=gt,
               I0=band_I[w_cross],anti=band_anti[w_cross],core=band_core[w_cross],
               wk=w_cross-k,log2n=math.log2(n))
    if w_cross:
        even = (w_cross % 2 == 0)
        mann = "CLOSES (I0==anti)" if band_anti[w_cross]==band_I[w_cross] else \
               ("anti-core+<=1 CLOSES" if band_core[w_cross]==band_I[w_cross] else "UNDERCOUNTS")
        print(f"  delta*={dstar:.4f} gt={gt}  w_cross={w_cross}({'EVEN' if even else 'ODD'})  "
              f"w_cross-k={w_cross-k} vs log2(n)={math.log2(n):.0f}")
        print(f"  MANN at crossing: I0={band_I[w_cross]} anti-closed={band_anti[w_cross]} "
              f"anti-core+<=1={band_core[w_cross]} -> {mann}")
        out['mann_full']=band_anti[w_cross]==band_I[w_cross]
        out['mann_core']=band_core[w_cross]==band_I[w_cross]
        out['even']=even
    return out

def main():
    GT = {(8,2):0.375,(8,4):0.25,(16,4):0.5625,(16,8):0.3125}
    cases = [(8,2),(8,4),(16,2),(16,4),(16,8),(16,12)]
    if len(sys.argv) > 1:
        cases = [tuple(int(x) for x in sys.argv[1].split(','))]
    rows = [analyze(n,k,GT.get((n,k))) for (n,k) in cases]
    print("\n===== A2 SUMMARY: does Mann/antipodal close the crossing? =====")
    print(" n  k  rho    w_cross parity  I0  anti  core  Mann_full Mann_core | wc-k log2n")
    for r in rows:
        if r['w_cross'] is None: continue
        print(f"{r['n']:3d}{r['k']:3d} {r['rho']:5.3f}  {r['w_cross']:5d}  {'EVEN' if r['even'] else 'ODD ':>4}  "
              f"{r['I0']:4d} {r['anti']:4d} {r['core']:4d}  {str(r['mann_full']):>5}    {str(r['mann_core']):>5}   "
              f"| {r['wk']:3d}  {r['log2n']:.0f}")

if __name__ == "__main__":
    main()

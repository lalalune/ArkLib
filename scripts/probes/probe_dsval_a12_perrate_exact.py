#!/usr/bin/env python3
"""
A12 PER-RATE EXACT delta*(n,rho) -- char-0 worst-direction over-determined far-line incidence.

THE OPEN VALUE (issue #407, combinatorial & q-independent):
  Domain mu_n = 2-power mult. subgroup (n=2^a). RS[mu_n, k=rho*n].
  Direction (a,b), k <= a < b < n far exponents. Line f_gamma = x^a + gamma*x^b.
  K(a,b,w) = #{ distinct gamma : f_gamma agrees with SOME deg-<k poly on a w-subset S of mu_n }.
  I(w) = max over directions (a,b) of K(a,b,w).   delta = 1 - w/n.
  delta*(n,rho) = sup{ delta : I(delta) <= budget = n }.

EXACT mechanism (no F_p sweep). f_gamma agrees with deg-<k poly on S (|S|=w) iff the restricted
values  v_S = x^a|_S + gamma * x^b|_S  lie in the deg-<k space on S. Let C be the (w-k)-dim dual
(parity-check rows over S that annihilate deg-<k). Agreement <=>  C . v_S = 0, i.e. for every
dual row c:   <c, x^a|_S> + gamma <c, x^b|_S> = 0.
  - w = k+1 : one dual row -> gamma = -<c,x^a>/<c,x^b> (one gamma per S, generically; the underdet
              boundary).
  - w >= k+2 (OVER-DETERMINED, depth s-k>=... ): need a COMMON gamma solving all w-k equations,
              i.e. the two vectors P_a = (C x^a|_S), P_b = (C x^b|_S) in F^{w-k} must be PARALLEL,
              and then gamma = -P_a[j]/P_b[j] (consistent j). At most ONE gamma per consistent S.
K(a,b,w) = #{ distinct gamma values realized over all w-subsets S }. This is the dilation-orbit
count. We compute it EXACTLY over a big prime q >> n^4 (over-det band is proven p-independent;
char-0 faithful), and CROSS-CHECK on a second prime.

Per-rate table for n=8,16 (full subset enumeration), n=32 sampled where feasible.
"""

import itertools
from math import gcd, comb
import sys

PRIMES = {
    8:  (1099511627873, 1099512676457),
    16: (1099511627873, 1099512676609),
    32: (1099511627873, 1099513724929),
    64: (1099511628161, 1099513724929),
}

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31):
        if m % p == 0: return m == p
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else:
            return False
    return True

def find_gen(p, n):
    g0 = 2
    while True:
        w = pow(g0, (p-1)//n, p)
        if pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in range(2, n) if n % q == 0 and is_prime(q)):
            return w
        g0 += 1

def dual_basis_on_S(Hs, k, p):
    """Basis of the dual (parity checks) of deg-<k RS restricted to point-set Hs (|S|=w).
    Vandermonde V (w x k), V[i][j] = Hs[i]^j. Dual = left null space of V (dim w-k).
    Return list of dual rows (length w each)."""
    w = len(Hs)
    # Build V (w x k), reduce its transpose to find left null space of V <=> null space of V^T acting...
    # left null space of V: vectors c (len w) with c^T V = 0  <=> V^T c = 0 (k x w system).
    # Solve V^T c = 0 over F_p: basis of null space of the k x w matrix M = V^T.
    M = [[pow(Hs[i], j, p) for i in range(w)] for j in range(k)]  # k x w
    return nullspace(M, w, p)

def nullspace(M, ncols, p):
    """Null space basis of matrix M (rows) over F_p; M has ncols columns."""
    M = [row[:] for row in M]
    nrows = len(M)
    pivot_col = {}
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] % p != 0:
                piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p-2, p)
        M[r] = [(x*inv) % p for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(M[i][j]-f*M[r][j]) % p for j in range(ncols)]
        pivot_col[c] = r
        r += 1
        if r == nrows: break
    pivots = set(pivot_col.keys())
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fcol in free:
        vec = [0]*ncols
        vec[fcol] = 1
        for c, row in pivot_col.items():
            vec[c] = (-M[row][fcol]) % p
        basis.append(vec)
    return basis

def gammas_for_subset(Hs, va, vb, k, p):
    """Distinct gamma (nonzero) such that va + gamma*vb is deg-<k on point-set Hs (over-det aware).
    Returns set of gamma in F_p. va,vb are x^a,x^b restricted to S (lists len w)."""
    w = len(Hs)
    if w <= k:
        return None  # underdetermined trivially: any gamma works -> not a finite incidence; skip
    C = dual_basis_on_S(Hs, k, p)  # (w-k) rows, each len w
    # Pa[t] = <C[t], va>, Pb[t] = <C[t], vb>
    Pa = [sum(C[t][i]*va[i] for i in range(w)) % p for t in range(len(C))]
    Pb = [sum(C[t][i]*vb[i] for i in range(w)) % p for t in range(len(C))]
    # need gamma with Pa[t] + gamma*Pb[t] = 0 for ALL t.
    # collect constraints
    gamma = None
    for t in range(len(C)):
        if Pb[t] % p == 0:
            if Pa[t] % p != 0:
                return set()  # inconsistent: 0 = nonzero
            # else 0=0, no constraint
        else:
            g = (-Pa[t]) * pow(Pb[t], p-2, p) % p
            if gamma is None:
                gamma = g
            elif gamma != g:
                return set()  # inconsistent
    if gamma is None:
        # all Pb=0 and all Pa=0: va,vb both already deg-<k on S -> jointAgree (degenerate),
        # EXCLUDE per Def (the line agrees but it's the trivial joint-agreement case).
        return set()
    if gamma == 0:
        return set()  # gamma=0 is pure monomial x^a; exclude degenerate
    return {gamma}

def incidence(p, n, k, a, b, w):
    """K(a,b,w) = # distinct gamma realized over all w-subsets S of mu_n."""
    wn = find_gen(p, n); H = [pow(wn, i, p) for i in range(n)]
    xa = [pow(x, a, p) for x in H]; xb = [pow(x, b, p) for x in H]
    seen = set()
    for S in itertools.combinations(range(n), w):
        Hs = [H[i] for i in S]; va = [xa[i] for i in S]; vb = [xb[i] for i in S]
        gs = gammas_for_subset(Hs, va, vb, k, p)
        if gs: seen |= gs
    return len(seen)

def deltastar_for_n(p, n, k, directions=None):
    if directions is None:
        directions = [(a,b) for a in range(k, n) for b in range(a+1, n)]
    # scan w from n down. I(w)=max_dir K. delta=1-w/n. Larger delta = smaller w = larger K.
    # delta* = largest delta (smallest w) with I(w) <= budget n.
    budget = n
    perw = {}
    for w in range(n, k, -1):
        bestK = 0; argd = None; perdir = {}
        for (a,b) in directions:
            K = incidence(p, n, k, a, b, w)
            perdir[(a,b)] = K
            if K > bestK: bestK = K; argd = (a,b)
        perw[w] = (bestK, argd, perdir)
    # find smallest w with I<=n (largest delta)
    ds=None; dsdir=None; dsw=None
    for w in range(k+1, n+1):  # increasing w = decreasing delta
        I, argd, _ = perw[w]
        if I <= budget:
            ds = 1 - w/n; dsdir = argd; dsw = w
            break
    return ds, dsdir, dsw, perw

def main():
    RATES = [("1/2", 2), ("1/4", 4), ("1/8", 8), ("1/16", 16)]
    NS = [8, 16]
    show_table = False
    args = [x for x in sys.argv[1:] if not x.startswith("-")]
    if "--table" in sys.argv: show_table = True
    if args: NS = [int(x) for x in args[0].split(",")]
    print("="*96)
    print("A12 PER-RATE EXACT delta*(n,rho) -- char-0 worst-direction far-line incidence (budget=n)")
    print("="*96)
    for n in NS:
        p1, p2 = PRIMES[n]
        print(f"\n##### n={n}  primes q1={p1} q2={p2}  (both >> n^4={n**4}) #####")
        print(f"  {'rho':>5} {'k':>3} {'cap':>7} {'delta*':>8} {'dir(a,b)':>10} {'w*':>4} "
              f"{'good_band':>9} {'gap2cap':>8}  {'q-indep':>8}")
        for (rlabel, rd) in RATES:
            k = n // rd
            if k < 1 or k >= n: continue
            rho = k/n; cap = 1-rho
            ds1, dir1, w1, perw1 = deltastar_for_n(p1, n, k)
            ds2, dir2, w2, _ = deltastar_for_n(p2, n, k)
            qok = "YES" if (abs((ds1 or -9)-(ds2 or -9))<1e-12) else f"NO({ds2})"
            band = (n - w1) if w1 else 0  # number of corrupted coords = n - w*
            print(f"  {rlabel:>5} {k:>3} {cap:>7.4f} {ds1:>8.4f} {str(dir1):>10} {w1:>4} "
                  f"{band:>3}/{n:<5} {cap-ds1:>8.4f}  {qok:>8}")
            if show_table:
                for w in range(n, k, -1):
                    I, argd, _ = perw1[w]
                    print(f"        w={w:>3} delta={1-w/n:.4f}  I={I:>4}  dir={argd}")
    print("\nReading: delta*=1-w*/n, w*=smallest window size whose worst-direction incidence <= n.")
    print("good_band = n - w* = max corrupted coords still under budget. q-indep cross-checked on 2 primes.")

if __name__ == "__main__":
    main()

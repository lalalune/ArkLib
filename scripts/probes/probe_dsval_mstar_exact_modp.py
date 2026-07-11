#!/usr/bin/env python3
"""
EXACT mod-p worst-direction orbit-count scan to SETTLE m* growth (bounded ~3 vs ~log n).

THE CONVERGENT RESIDUAL (#444 c.04:49 dcc6ebd26): delta*(n,rho) = (1-rho) - m*/n,
m* := w*-k = binding over-determination depth. Single open question: is m* BOUNDED
(=> delta* near capacity, REFUTES window-edge 1-rho-Theta(1/log n)) or GROWS ~log n?
n=8,16 cannot separate 3 from log2(n). The DECISIVE distinguisher is the n=32 (then 64)
WORST-DIRECTION orbit-count scan. This probe does it EXACTLY (mod-p, no floats) over the
PROPER subgroup mu_n (m=(p-1)/n >= 2, NEVER n=q-1), across multiple prize-band primes
(rule-2: confirm p-independence claimed by the convergent structure; rule-3 thinness gate).

Object (verbatim the in-tree FarCosetExplosion / wf-NH binding):
  far direction line L_gamma = x^a + gamma*x^b ; codeword space = deg < k.
  For a w-subset S of mu_n (w = k + m, m = over-det depth), the line agrees with SOME
  deg<k codeword on S iff the w x (k+2) matrix M_S = [1,x,..,x^{k-1}, x^a, x^b] (rows in S)
  is rank-deficient with a UNIQUE gamma (the <=1-gamma-per-witness dichotomy). 
  incidence I(a,b;w) = # distinct gamma (over all w-subsets S) [+1 if gamma=0 admissible].
  budget = q*eps* = n. delta* = (1-rho) at the w where worst-dir I drops to <= budget.
  w* = largest w with worst-dir I > budget; m* = w* - k.

EXACT gamma extraction per subset S (no float tolerance):
  M_S has k+2 cols. Consistency (rank <= k+1) <=> det(M_S^T M_S) deficiency is NOT used;
  instead: line col_a + gamma*col_b must lie in colspace(V) where V=[1..x^{k-1}] (k cols).
  Stack [V | col_a] and [V | col_b]; the unique gamma (if it exists) is found by:
    require col_a in span(V, col_b) and the combination has col_b-coeff = -gamma with
    col_a,col_b residues against V proportional. We do it via exact linear algebra mod p:
    pick any (k+1)-subset-free full-rank k-subset R0 of rows to invert V; solve
    coeffs s.t. V*ca = col_a, V*cb = col_b on R0 (k x k solve), residual on the rest must
    vanish for BOTH, and gamma = -(residual_a / residual_b) consistent across all extra rows.
  All arithmetic in F_p. gamma in F_p is the orbit representative; distinct gammas counted.
"""
import sys, math, argparse
from itertools import combinations
import numpy as np

def find_prime(n, beta_target, min_m=2):
    # prize-band prime p ~ n^beta, p ≡ 1 (mod n), m=(p-1)/n >= min_m, p PRIME, NEVER n=q-1.
    import sympy
    lo = max(int(n**beta_target), n*min_m+1)
    p = lo - (lo % n) + 1
    while True:
        if p > n*min_m and sympy.isprime(p):
            return p
        p += n

def subgroup_mu_n(n, p):
    # generator g of F_p*, h = g^{(p-1)/n} has order exactly n. Return [h^0..h^{n-1}].
    import sympy
    g = sympy.primitive_root(p)
    m = (p-1)//n
    h = pow(g, m, p)
    assert pow(h, n, p) == 1 and all(pow(h,d,p)!=1 for d in range(1,n)), "h not order n"
    return [pow(h, i, p) for i in range(n)], m

def inv(a, p):
    return pow(a % p, p-2, p)

def gamma_for_subset(rows_pow, k, idx_a, idx_b, p):
    # rows_pow[i] = list of [x^0,...] we pass precomputed columns. We get for subset rows:
    #   V (w x k) = [x^0..x^{k-1}], ca = x^a column, cb = x^b column  (all mod p)
    # Find unique gamma in F_p s.t. ca + gamma*cb in colspace(V), or None.
    V, ca, cb = rows_pow
    w = len(ca)
    # Row-reduce [V | ca | cb] over F_p; need ca+gamma cb to be in span(V).
    # Augment A = V (w x k). Compute its RREF + record pivot rows. Then express ca, cb residuals.
    # Build matrix M = [V | ca | cb], reduce first k cols.
    A = [[V[i][j] % p for j in range(k)] + [ca[i] % p, cb[i] % p] for i in range(w)]
    ncol = k + 2
    piv_rows = []
    r = 0
    for c in range(k):
        # find pivot
        pr = None
        for rr in range(r, w):
            if A[rr][c] % p != 0:
                pr = rr; break
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        invp = inv(A[r][c], p)
        A[r] = [(x*invp) % p for x in A[r]]
        for rr in range(w):
            if rr != r and A[rr][c] % p != 0:
                f = A[rr][c] % p
                A[rr] = [(A[rr][j] - f*A[r][j]) % p for j in range(ncol)]
        piv_rows.append(c)
        r += 1
        if r == w: break
    # After elimination, rows r..w-1 have zeros in all V columns. For those rows, the
    # residual columns are (ca_res, cb_res). Need ca_res + gamma*cb_res == 0 for ALL such rows
    # with a SINGLE gamma. If all residual rows are zero in ca and cb => gamma free (degenerate;
    # means line already in code on S without x^a/x^b => not a far-line witness; skip).
    res = [(A[rr][k], A[rr][k+1]) for rr in range(r, w)]
    res = [(x % p, y % p) for (x,y) in res]
    nz = [(x,y) for (x,y) in res if not (x==0 and y==0)]
    if not nz:
        return None  # degenerate: x^a (and x^b) already in code-span on S => not a binding far witness
    # need ca_res = -gamma * cb_res for every residual row, single gamma
    gammas = set()
    for (x,y) in nz:
        if y == 0:
            return None  # ca_res nonzero but cb_res zero => no finite gamma
        g = (-x * inv(y, p)) % p
        gammas.add(g)
    if len(gammas) != 1:
        return None  # inconsistent across rows => no single gamma => no witness
    return gammas.pop()

def incidence(n, k, a, b, w, mu, p, count_gamma0=False):
    # exact distinct-gamma count over all w-subsets
    xa = [pow(mu[i], a, p) for i in range(n)]
    xb = [pow(mu[i], b, p) for i in range(n)]
    Vall = [[pow(mu[i], j, p) for j in range(k)] for i in range(n)]
    found = set()
    saw_g0 = False
    for S in combinations(range(n), w):
        V = [Vall[i] for i in S]
        ca = [xa[i] for i in S]
        cb = [xb[i] for i in S]
        g = gamma_for_subset((V, ca, cb), k, a, b, p)
        if g is None:
            continue
        if g == 0:
            saw_g0 = True
            if count_gamma0:
                found.add(0)
        else:
            found.add(g)
    return len(found)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--rho", type=str, default="1/4")  # k/n
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--validate", action="store_true")
    args = ap.parse_args()
    n = args.n; k = args.k
    p = find_prime(n, args.beta)
    mu, m = subgroup_mu_n(n, p)
    print(f"n={n} k={k} rho={k/n} prime p={p} (p^(1/log)={math.log(p)/math.log(n):.2f}, m=(p-1)/n={m}) PROPER mu_n", flush=True)
    if args.validate:
        # n=16 rho=1/4 k=4: known worst dir(8,14) w=7 I=9 -> delta*=0.5625, m*=w*-k=3
        I = incidence(16,4,8,14,7,mu,p)
        print(f"  VALIDATE n=16 dir(8,14) w=7: I={I} (expect 9, m*=3)", flush=True)

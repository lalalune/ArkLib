"""
maxlist_core.py  —  exact RS max-list machinery for the proximity-floor disproof search.

Setup (matches in-tree conventions, cf. probe_midband_extremal.py):
  - F_q prime field; mu_n = order-n=2^mu multiplicative subgroup (eval domain).
  - codeword = deg<k polynomial evaluated on mu_n.  rho = k/n.
  - list(w,a) = #{ codewords c : agree(c,w) >= a }   (agreement = #points where equal).
  - window in AGREEMENT: interior = rho*n < a < sqrt(rho)*n  (between capacity rho*n
    and Johnson sqrt(rho)*n).

EXACT counting (no q^k enumeration):
  A deg<k poly is determined by its values on any k of the n points (interpolation).
  Every codeword that agrees with w on a set S (|S|=a>=k) is the unique interpolant of
  w restricted to any k-subset of S that happens to reproduce w on all of S.
  => list(w,a) = #{ deg<k polys c : |{i: c(x_i)=w(i)}| >= a }
  We count DISTINCT such polynomials by their full agreement pattern, enumerating
  candidate interpolants from k-subsets of indices (de-duplicated by coefficient tuple).
  This is exact whenever a >= k (always true here: interior a > rho*n = k).
"""
import itertools, math
from functools import lru_cache

# ---------- field / subgroup ----------
def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def is_pow2plus1(x):
    y = x-1
    return y > 0 and (y & (y-1)) == 0

def find_mun(q, n):
    """generator g of order exactly n, and the subgroup list [g^0..g^{n-1}]."""
    for g in range(2, q):
        if pow(g, n, q) != 1: continue
        ok = True
        for d in range(1, n):
            if n % d == 0 and d < n and pow(g, d, q) == 1:
                ok = False; break
        if ok:
            sub = [pow(g, j, q) for j in range(n)]
            assert len(set(sub)) == n
            return g, sub
    raise RuntimeError(f"no order-{n} element in F_{q}")

# ---------- linear algebra mod q (interpolation) ----------
def interp_poly(xs, ys, q, k):
    """Unique deg<len(xs) poly through (xs,ys). Returns coeff list (low->high) of length len(xs),
    or None if singular (won't happen for distinct xs). We only ever pass len==k distinct points."""
    m = len(xs)
    # Vandermonde solve via Gaussian elimination mod q (q prime).
    A = [[pow(xs[r], c, q) for c in range(m)] + [ys[r] % q] for r in range(m)]
    for col in range(m):
        piv = None
        for r in range(col, m):
            if A[r][col] % q != 0:
                piv = r; break
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], q-2, q)
        A[col] = [(v*inv) % q for v in A[col]]
        for r in range(m):
            if r != col and A[r][col] % q != 0:
                f = A[r][col]
                A[r] = [(A[r][cc] - f*A[col][cc]) % q for cc in range(m+1)]
    return tuple(A[r][m] % q for r in range(m))

def eval_poly(coeffs, x, q):
    v = 0
    for c in reversed(coeffs):
        v = (v*x + c) % q
    return v

# ---------- exact list counting ----------
def list_size_exact(w, a, sub, q, k, cap=None):
    """
    Exact list(w,a) for a>=k. Enumerate candidate codewords as interpolants of w over
    k-subsets of agreement; de-dup by coeff tuple; count those agreeing on >=a points.
    Cost ~ C(n,k) interpolations. Fine for n<=32, k<=8 small subsets but C(32,16) is huge.
    Use only when C(n,k) is tractable; otherwise use list_size_cluster / sampled bounds.
    """
    n = len(sub)
    seen = set()
    cnt = 0
    for idx in itertools.combinations(range(n), k):
        xs = [sub[i] for i in idx]
        ys = [w[i] for i in idx]
        c = interp_poly(xs, ys, q, k)
        if c is None or c in seen:
            continue
        seen.add(c)
        ag = 0
        for i in range(n):
            if eval_poly(c, sub[i], q) == w[i]:
                ag += 1
        if ag >= a:
            cnt += 1
        if cap is not None and cnt >= cap:
            return cnt
    return cnt

def agreement(coeffs, w, sub, q):
    return sum(1 for i in range(len(sub)) if eval_poly(coeffs, sub[i], q) == w[i])

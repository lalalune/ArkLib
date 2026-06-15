#!/usr/bin/env python3
"""
Probe for CONJECTURE C10 (Gupta-Zagier Char-0 Crossing Pin):
  CLAIM: worst-case far-line list size at radius delta = #distinct r-fold dyadic-subgroup
         sumset = binom(n/2, r) in char 0; binom(n/2,r) <= q*eps* gives crossing
         n(cap - delta*) = w - k = log2(n), pinning delta* = (1-rho) - log2(n)/n PAST Johnson,
         char-independent for p ndvd D (D a power of 2).

This probe tests the THREE load-bearing sub-claims of C10, over PROPER subgroups mu_n
(n = 2^mu | p-1, p PRIME, p >> n^3, NEVER n = p-1):

  (S1) the DISTINCT r-fold SUMSET count of mu_n (n-th roots of unity in char 0) = binom(n/2, r)?
  (S2) the CROSSING arithmetic: does binom(n/2,r) <= q*eps* really pin delta* PAST Johnson,
       or does it land at/below Johnson (the Plotkin proxy horn)?
  (S3) the actual worst-case FAR-LINE incidence I(delta) over mu_n in char p -- is it
       governed by binom(n/2,r), or by the antipodal cubic n^3/32 (in-tree closed form)?

Honesty: proper subgroup, p prime, p >> n^3, never n = p-1. Reproducible. No fabrication.
"""
import itertools
import math
from sympy import isprime, primitive_root

def find_prime_with_subgroup(n, min_ratio=3):
    """Smallest prime p with n | p-1 and p > n^min_ratio (p >> n^3). Returns p."""
    target = n ** min_ratio
    # p = 1 + n*t, want p prime and p > target
    t = max(2, (target // n) + 1)
    while True:
        p = 1 + n * t
        if p > target and isprime(p):
            return p
        t += 1

def subgroup_mu_n(p, n):
    """The unique multiplicative subgroup of order n in F_p^*."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    return [pow(h, j, p) for j in range(n)]

# ---------- S1: char-0 distinct r-fold sumset count of the n-th roots of unity ----------
def distinct_rfold_sumset_char0(n, r):
    """
    |{ zeta^{i1} + ... + zeta^{ir} : 0<=i1<=...<=ir<n }| as DISTINCT complex values,
    zeta = exp(2pi i/n). Multisets of size r from the n roots, count distinct sums.
    We compare against binom(n/2, r) (C10's half-basis closed form) AND
    against binom(n, r) (naive) and the antipodal-collapsed count.
    """
    import cmath
    zeta = [cmath.exp(2j * math.pi * k / n) for k in range(n)]
    sums = set()
    for combo in itertools.combinations_with_replacement(range(n), r):
        s = sum(zeta[k] for k in combo)
        # round to kill float noise
        sums.add((round(s.real, 8), round(s.imag, 8)))
    return len(sums)

# ---------- S3: actual far-line incidence over mu_n in char p ----------
def rs_close(vec_vals, domain, p, k, r):
    """
    Is the function (domain -> vec_vals) within Hamming distance r of RS[k] over F_p
    on the n=|domain| points? i.e. EXISTS a poly of deg < k agreeing on >= n - r points.
    Correct test: for every k-subset that determines a unique deg<k poly, count agreements;
    a codeword within distance r exists iff some deg<k poly agrees on >= n-r coords.
    Enumerate candidate polys via k-subset interpolation (every closest codeword agrees on
    >= n-r >= k points, so its interpolation set is among the k-subsets we try).
    """
    n = len(domain)
    need = n - r
    if need <= k:
        return True  # trivially: any k points interpolate; >=need agreements achievable
    from itertools import combinations
    pts = list(range(n))
    for ksub in combinations(pts, k):
        coeffs = interpolate(ksub, domain, vec_vals, p, k)
        if coeffs is None:
            continue
        agree = sum(1 for i in pts
                    if eval_poly(coeffs, domain[i], p) == vec_vals[i] % p)
        if agree >= need:
            return True
    return False

def eval_poly(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc

def interpolate(ksub, domain, vals, p, k):
    """Unique deg<k poly through the k points; coeffs list length k, or None if singular."""
    rows = []
    for idx in ksub:
        x = domain[idx]
        rows.append([pow(x, j, p) for j in range(k)] + [vals[idx] % p])
    return solve_mod_p(rows, p, k)

def solve_mod_p(rows, p, k):
    rows = [r[:] for r in rows]
    for col in range(k):
        piv = None
        for r in range(col, len(rows)):
            if rows[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        inv = pow(rows[col][col], p - 2, p)
        rows[col] = [(v * inv) % p for v in rows[col]]
        for r in range(len(rows)):
            if r != col and rows[r][col] % p != 0:
                f = rows[r][col]
                rows[r] = [(rows[r][c] - f * rows[col][c]) % p for c in range(k + 1)]
    return [rows[i][k] for i in range(k)]

def poly_fits(sub, domain, vals, p, k):
    """Does a poly of deg < k pass through all points in 'sub'? (k unknowns, |sub| eqns)"""
    if len(sub) <= k:
        return True  # k unknowns, <=k constraints: generically solvable / deg<k interpolation
    # Build Vandermonde over F_p and check consistency (rank check via Gaussian elim mod p)
    rows = []
    for idx in sub:
        x = domain[idx]
        row = [pow(x, j, p) for j in range(k)] + [vals[idx] % p]
        rows.append(row)
    return consistent_mod_p(rows, p)

def consistent_mod_p(rows, p):
    """Gaussian elimination over F_p; return True iff system is consistent (no 0=nonzero row)."""
    rows = [r[:] for r in rows]
    ncols = len(rows[0]) - 1
    pivot_row = 0
    for col in range(ncols):
        piv = None
        for r in range(pivot_row, len(rows)):
            if rows[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            continue
        rows[pivot_row], rows[piv] = rows[piv], rows[pivot_row]
        inv = pow(rows[pivot_row][col], p - 2, p)
        rows[pivot_row] = [(v * inv) % p for v in rows[pivot_row]]
        for r in range(len(rows)):
            if r != pivot_row and rows[r][col] % p != 0:
                f = rows[r][col]
                rows[r] = [(rows[r][c] - f * rows[pivot_row][c]) % p for c in range(ncols + 1)]
        pivot_row += 1
    for r in rows:
        if all(r[c] % p == 0 for c in range(ncols)) and r[ncols] % p != 0:
            return False
    return True

def far_line_incidence(p, domain, n, k, a, b, r):
    """
    I(a,b; r) = #{ gamma in F_p : x^a + gamma x^b is within Hamming dist r of RS[k] on mu_n }.
    Direct enumeration over all gamma. (tiny n only)
    """
    cnt = 0
    for gamma in range(p):
        vals = [(pow(x, a, p) + gamma * pow(x, b, p)) % p for x in domain]
        if rs_close(vals, domain, p, k, r):
            cnt += 1
    return cnt

# ====================================================================
if __name__ == "__main__":
    print("=" * 78)
    print("C10 PROBE: Gupta-Zagier char-0 crossing pin delta* = (1-rho) - log2(n)/n")
    print("=" * 78)

    # ---- S1: distinct r-fold sumset count vs binom(n/2, r) ----
    print("\n[S1] char-0 distinct r-fold SUMSET count of n-th roots vs binom(n/2, r):")
    print(f"{'n':>4} {'r':>3} {'distinct':>10} {'binom(n/2,r)':>13} {'binom(n,r)':>11} {'match n/2?':>10}")
    for n in [8, 16]:
        for r in range(2, 5):
            d = distinct_rfold_sumset_char0(n, r)
            bnh = math.comb(n // 2, r)
            bn = math.comb(n, r)
            print(f"{n:>4} {r:>3} {d:>10} {bnh:>13} {bn:>11} {str(d == bnh):>10}")

    # ---- S2: the crossing arithmetic ----
    print("\n[S2] CROSSING arithmetic: binom(n/2,r) <= q*eps* -> claimed delta* vs Johnson:")
    print("  prize: eps*=2^-128, q ~ n*2^128 (so q*eps* ~ n = budget).")
    print(f"{'n':>6} {'rho':>5} {'r*=cross':>9} {'delta*_claim':>13} {'Johnson':>9} {'cap':>6} {'past J?':>8}")
    eps = 2.0 ** -128
    for mu in [10, 20, 30]:
        n = 2 ** mu
        for rho in [0.5, 0.25, 0.125, 0.0625]:
            k = rho * n
            q = n * 2.0 ** 128          # critical field: budget B = q*eps* = n
            budget = q * eps             # = n
            # crossing r*: smallest r with binom(n/2, r) <= budget.
            # log binom(n/2, r) ~ r*log2(n/2) for r << n/2. binom(n/2,r) <= budget=n
            # => r * log2(n/2) <~ log2(n)  => r ~ log2(n)/log2(n/2) ~ 1.  So r* is tiny.
            # find r* by log-binomial
            def log2binom(N, rr):
                return sum(math.log2(N - i) - math.log2(i + 1) for i in range(rr))
            rstar = None
            for rr in range(1, n // 2):
                if log2binom(n // 2, rr) <= math.log2(budget):
                    rstar = rr
                    break
                # we want the crossing: largest r with binom > budget, then r* = that+1.
            # Actually crossing: binom decreasing in r? No, increasing then symmetric.
            # binom(n/2,r) is INCREASING for r < n/4. So "binom <= budget" holds for SMALL r.
            # The list size at radius delta with r errors: far-line list ~ binom(n/2, r) where
            # r = n - s, s = agreement. Closeness radius delta = r/n. Budget crossing:
            # largest r (=most errors / largest delta) with binom(n/2,r) <= budget.
            rstar = 0
            for rr in range(0, n // 2 + 1):
                if log2binom(n // 2, rr) <= math.log2(budget):
                    rstar = rr
                else:
                    break
            # C10 claims crossing at n(cap - delta*) = log2(n), delta* = (1-rho) - log2(n)/n
            delta_claim = (1 - rho) - math.log2(n) / n
            johnson = 1 - math.sqrt(rho)
            cap = 1 - rho
            # the ACTUAL delta from the crossing r*: delta = r*/n
            delta_from_cross = rstar / n
            past = delta_claim > johnson
            print(f"{n:>6.0e} {rho:>5} {rstar:>9} {delta_claim:>13.6f} {johnson:>9.6f} {cap:>6.4f} {str(past):>8}  (delta_from_r*/n={delta_from_cross:.6f})")

    # ---- S3: actual far-line incidence over a proper subgroup, char p ----
    print("\n[S3] ACTUAL worst-case far-line incidence over PROPER mu_n (p prime, p>>n^3):")
    print(f"{'n':>4} {'p':>9} {'k':>3} {'r':>3} {'max I(a,b)':>11} {'argmax(a,b)':>13} {'binom(n/2,r)':>13} {'n^3/32':>8}")
    print("  (FAR directions only: a,b >= k so the monomial pencil is genuinely far from RS[k])")
    for n in [8]:
        p = find_prime_with_subgroup(n, min_ratio=3)
        domain = subgroup_mu_n(p, n)
        assert len(set(domain)) == n and p % n == 1 and p != n + 1
        for k in [2]:               # rho = 1/4
            for r in [2, 3]:        # radius -> over-det s = n - r vs k
                best = -1
                arg = None
                for a in range(k, n):       # FAR: exponents >= k
                    for b in range(k, n):
                        if a == b:
                            continue
                        I = far_line_incidence(p, domain, n, k, a, b, r)
                        if I > best:
                            best = I
                            arg = (a, b)
                bnh = math.comb(n // 2, r)
                # in-tree closed form for s=k+2 over-det max at k=2: 2m^3-2m^2+1, m=n/4
                m = n // 4
                overdet = 2 * m**3 - 2 * m**2 + 1
                print(f"{n:>4} {p:>9} {k:>3} {r:>3} {best:>11} {str(arg):>13} {bnh:>13} {n**3/32:>8.1f}  (in-tree s=k+2 max={overdet})")
    print("\nDONE.")

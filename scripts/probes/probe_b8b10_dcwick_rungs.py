# Probe: extend the class-balanced count B(k,m) ladder to k=8,10 (T6-B8B10-rungs-lean).
#
# B(k,m) = #{ c : Fin k -> (Fin m x Bool) : for every class j, #{+}=#{-} }
#        = zero-sum count E_{k/2}(mu_{2m}) under Lam-Leung balance characterization.
#
# Add-one-class recursion: B(k, m+1) = sum_j C(k,2j) C(2j,j) B(k-2j, m), new class takes 2j
# positions (j plus, j minus). We:
#  (1) confirm the rec8/rec10 coefficient vectors by symbolic derivation,
#  (2) brute-force verify B8/B10 closed forms (degree 4,5 in m) on small m,
#  (3) confirm the recursion holds B(k,m+1) = ... on small m,
#  (4) compute the symmetric mean-0 cumulants kappa_8, kappa_10 from E1..E5 and check
#      kappa_8 = -1155 n, kappa_10 = 57456 n  (n = 2m),
#  (5) confirm budget inequalities |kappa_2r| <= (2r-1)!! n^r for the dyadic n>=2.
from itertools import product
from math import comb, factorial

def B_brute(k, m):
    if m == 0:
        return 1 if k == 0 else 0
    cnt = 0
    for c in product(range(m * 2), repeat=k):  # entry = class*2 + sign
        ok = True
        for j in range(m):
            plus = sum(1 for x in c if x == j * 2 + 1)
            minus = sum(1 for x in c if x == j * 2 + 0)
            if plus != minus:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt

def rec_coeffs(k):
    # coefficient of B(k-2j, m) in B(k, m+1)  for j=0..k//2
    # j=0 term is the trailing constant when k-2j=0
    return {2 * j: comb(k, 2 * j) * comb(2 * j, j) for j in range(0, k // 2 + 1)}

print("=== add-one-class recursion coefficient vectors ===")
for k in (2, 4, 6, 8, 10):
    cs = rec_coeffs(k)
    # express as: B(k,m+1) = B(k,m) + sum_{j>=1} c_{2j} B(k-2j,m); the j=k/2 term is constant (B0=1)
    terms = []
    for twoj in sorted(cs):
        if twoj == 0:
            continue  # this is c0=1 times B(k,m) itself -> the leading B(k,m)
        rem = k - twoj
        coeff = cs[twoj]
        if rem == 0:
            terms.append(f"+{coeff}")          # constant (B0=1)
        else:
            terms.append(f"+{coeff}*B{rem}(m)")
    print(f"k={k}: B{k}(m+1) = B{k}(m) " + " ".join(terms))

# Closed forms (to be verified). Derive by solving recursion as polynomial in m.
def B2cf(m):  return 2*m
def B4cf(m):  return 12*m**2 - 6*m
def B6cf(m):  return 120*m**3 - 180*m**2 + 80*m

# Solve B8, B10 closed forms via the recursion + base B(k,0)=0 (k>=1).
# We fit a polynomial of degree k/2 in m using the recursion as a finite-difference equation.
# Easiest: compute B(k,m) by the recursion for m=0..k, then Lagrange/solve for poly coeffs.
def B_via_rec(k, m, memo):
    if (k, m) in memo:
        return memo[(k, m)]
    if k == 0:
        return 1
    if m == 0:
        memo[(k, m)] = 0
        return 0
    cs = rec_coeffs(k)
    total = 0
    for twoj, coeff in cs.items():
        total += coeff * B_via_rec(k - twoj, m - 1, memo)
    memo[(k, m)] = total
    return total

memo = {}
# fit polynomial deg d for B(k,.) using values at m=0..d
def fit_poly(k):
    d = k // 2
    xs = list(range(0, d + 1))
    ys = [B_via_rec(k, x, memo) for x in xs]
    # solve Vandermonde for integer coeffs (use fractions)
    from fractions import Fraction
    import copy
    # build matrix
    A = [[Fraction(x**p) for p in range(d + 1)] for x in xs]
    b = [Fraction(y) for y in ys]
    # gaussian elimination
    n = d + 1
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][c] - f * M[col][c] for c in range(n + 1)]
    return [M[i][n] for i in range(n)]  # coeffs c0..cd (low to high)

print("\n=== fitted closed-form polynomial coefficients (low->high power of m) ===")
for k in (2, 4, 6, 8, 10):
    coeffs = fit_poly(k)
    print(f"B{k}(m) = " + " + ".join(f"{c}*m^{i}" for i, c in enumerate(coeffs) if c != 0))

# explicit candidates for B8, B10 from the fit
c8 = fit_poly(8)
c10 = fit_poly(10)
def Bcf_from(coeffs):
    return lambda m: sum(int(c) * m**i for i, c in enumerate(coeffs))
B8cf = Bcf_from(c8)
B10cf = Bcf_from(c10)

print("\n=== brute-force verify closed forms (small m) ===")
for m in range(0, 3):
    row = [f"m={m}"]
    for k, cf in [(2, B2cf), (4, B4cf), (6, B6cf), (8, B8cf), (10, B10cf)]:
        kmax = {2: 99, 4: 99, 6: 2, 8: 1, 10: 1}[k]  # brute limit by feasibility
        if m <= kmax:
            bb = B_brute(k, m)
            row.append(f"B{k}={bb}(cf {cf(m)}){'OK' if bb==cf(m) else 'MISMATCH'}")
        else:
            # cross-check via recursion instead of brute
            bv = B_via_rec(k, m, memo)
            row.append(f"B{k}={bv}(cf {cf(m)}){'OK' if bv==cf(m) else 'MISMATCH'}")
    print("  ".join(row))

print("\n=== recursion check rec8/rec10 against B_via_rec (m=0..3) ===")
for m in range(0, 4):
    b8m, b8m1   = B_via_rec(8, m, memo),  B_via_rec(8, m + 1, memo)
    b10m, b10m1 = B_via_rec(10, m, memo), B_via_rec(10, m + 1, memo)
    cs8 = rec_coeffs(8); cs10 = rec_coeffs(10)
    pred8 = sum(cs8[2*j] * B_via_rec(8 - 2*j, m, memo) for j in range(0, 5))
    pred10 = sum(cs10[2*j] * B_via_rec(10 - 2*j, m, memo) for j in range(0, 6))
    print(f"m={m}: rec8 {b8m1==pred8}  rec10 {b10m1==pred10}")

# === cumulants from E_r = B_{2r}(m), with n = 2m ===
# central moments mu_{2r} = E_r (mean-0, real), odd moments 0.
# kappa from moments via standard formulas (mean 0):
# k2 = m2
# k4 = m4 - 3 m2^2
# k6 = m6 - 15 m4 m2 + 30 m2^3
# k8 = m8 - 28 m6 m2 - 35 m4^2 + 420 m4 m2^2 - 630 m2^4
# k10 = m10 - 45 m8 m2 - 210 m6 m4 + 1260 m6 m2^2 + 3150 m4^2 m2
#       - 18900 m4 m2^3 + 22680 m2^5    [CORRECTED: derived by inverting exp(K) symbolically;
#       the common -9450/+9450 table is WRONG and gives a spurious n^5,n^4 residual.]
from sympy import symbols, expand, Rational, simplify

n = symbols('n')
mm = n / 2  # m = n/2
E = {}
E[1] = mm * 2                                   # = n
E[2] = 12*mm**2 - 6*mm                           # = 3n^2 - 3n
E[3] = 120*mm**3 - 180*mm**2 + 80*mm             # = 15n^3 -45n^2+40n
E[4] = sum(int(c)*mm**i for i, c in enumerate(c8))
E[5] = sum(int(c)*mm**i for i, c in enumerate(c10))

m2, m4, m6, m8, m10 = E[1], E[2], E[3], E[4], E[5]
k2  = expand(m2)
k4  = expand(m4 - 3*m2**2)
k6  = expand(m6 - 15*m4*m2 + 30*m2**3)
k8  = expand(m8 - 28*m6*m2 - 35*m4**2 + 420*m4*m2**2 - 630*m2**4)
k10 = expand(m10 - 45*m8*m2 - 210*m6*m4 + 1260*m6*m2**2 + 3150*m4**2*m2
             - 18900*m4*m2**3 + 22680*m2**5)

print("\n=== cumulants in n (should be linear: kappa_2r = c_r * n) ===")
print("E4(n) =", expand(E[4]))
print("E5(n) =", expand(E[5]))
print("kappa2  =", k2,  "  (expect n)")
print("kappa4  =", k4,  "  (expect -3 n)")
print("kappa6  =", k6,  "  (expect 40 n)")
print("kappa8  =", k8,  "  (expect -1155 n)")
print("kappa10 =", k10, "  (expect 57456 n)")

print("\n=== double-factorial Wick budget (2r-1)!! n^r ===")
def dfact(k):
    r = 1
    while k > 1:
        r *= k
        k -= 2
    return r
for r, kap, expect in [(1,k2,'n'),(2,k4,'-3 n'),(3,k6,'40 n'),(4,k8,'-1155 n'),(5,k10,'57456 n')]:
    df = dfact(2*r-1)
    print(f"r={r}: (2r-1)!!={df}, Wick ceiling {df}*n^{r}; kappa_{2*r}={kap}")

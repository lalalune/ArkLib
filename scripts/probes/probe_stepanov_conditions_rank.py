#!/usr/bin/env python3
"""
PROBE the GENUINE open lever named in StepanovGenericInsufficiency:
the CONDITIONS-DEGENERACY COUNT on A = mu_n ∩ (mu_n + c).

Stepanov: seek nonzero Psi of degree < D, with Hasse derivatives
  (hasseDeriv j Psi)(a) = 0  for all a in A, all j < M.
That is  |A|*M  linear conditions on the D coefficients of Psi.
GENERIC engine: needs D > |A|*M to force a nonzero solution => r(c) <= D/M >= |A| (vacuous).

THE KEY QUESTION (the open core): on A, x^n=1 AND (c-x)^n=1, so the conditions are
DEGENERATE. The EFFECTIVE RANK rho(D,M) of the |A|*M x D Hasse-condition matrix may be
<< |A|*M. If rho(D,M) < D for some D << |A|*M (in fact D ~ n), a nonzero degree-D
auxiliary vanishing to order M exists => r(c)*M <= D => r(c) <= D/M, a REAL saving when D/M < |A|.

We MEASURE rho(D,M) exactly (mod p) over proper thin mu_n, p>>n^3, n=2^a, n|p-1, NEVER n=q-1,
sweeping M and reading the SMALLEST D with a nonzero kernel vector (rank-deficient), and
report the implied r(c) <= D/M vs the trivial |A| and the order-2 (n+1)/2.

If the effective rank is FULL (rho = min(|A|*M, D)) -> NO collapse -> wall confirmed (negative).
If rho < |A|*M with a structured deficiency -> the collapse is REAL and its LAW is the brick.
"""
import sympy as sp
from sympy import Matrix, binomial

def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f

def find_gen(p, n):
    pf = prime_factors(n)
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n//q, p)!=1 for q in pf):
            return cand
    raise RuntimeError((p,n))

def mu_n(p, n):
    g = find_gen(p, n)
    return [pow(g, i, p) for i in range(n)]

def find_prime(n, beta):
    target = n**beta
    k = max(1, target // n)
    while True:
        p = k*n + 1
        if p > 2*n**3 and sp.isprime(p):
            return p
        k += 1

def hasse_rank_modp(A, M, D, p):
    """Build the |A|*M x D matrix of Hasse conditions on coeffs c_0..c_{D-1}:
       row (a,j): coeff of c_e is binomial(e,j)*a^{e-j}.  Return rank mod p."""
    rows = []
    for a in A:
        for j in range(M):
            row = []
            for e in range(D):
                if e >= j:
                    row.append(int(binomial(e,j) % p) * pow(a, e-j, p) % p)
                else:
                    row.append(0)
            rows.append([x % p for x in row])
    Mx = Matrix(rows)
    # rank over GF(p)
    return Mx.rank(iszerofunc=lambda x: x % p == 0), len(rows)

# To get true GF(p) rank, do gaussian elimination mod p ourselves (sympy rank is over Q).
def rank_gfp(rows, p):
    rows = [r[:] for r in rows]
    nrows = len(rows); ncols = len(rows[0]) if rows else 0
    rank = 0
    pivcol = 0
    r = 0
    for col in range(ncols):
        # find pivot
        piv = None
        for i in range(r, nrows):
            if rows[i][col] % p != 0:
                piv = i; break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][col], p-2, p)
        rows[r] = [(x*inv) % p for x in rows[r]]
        for i in range(nrows):
            if i != r and rows[i][col] % p != 0:
                f = rows[i][col]
                rows[i] = [(rows[i][k] - f*rows[r][k]) % p for k in range(ncols)]
        r += 1
        rank += 1
        if r == nrows: break
    return rank

def conditions_rank(A, M, D, p):
    rows = []
    for a in A:
        for j in range(M):
            row = []
            for e in range(D):
                if e >= j:
                    row.append((int(binomial(e,j) % p) * pow(a, e-j, p)) % p)
                else:
                    row.append(0)
            rows.append(row)
    return rank_gfp(rows, p), len(rows)

def main():
    print("PROBE: effective rank of order-M Hasse conditions on A = mu_n ∩ (mu_n+c)")
    print("collapse => rho < |A|*M => degree-D auxiliary (D = rho+1) vanishes to order M")
    print("="*92)
    for n in [8, 16]:
        p = find_prime(n, 4)
        G = set(mu_n(p, n))
        # pick off-diagonal c maximizing |A| (the hardest = most representations)
        best = None
        for c in range(1, p):
            if pow(c, n, p) == 1: continue
            A = [x for x in G if ((x - c) % p) in G]
            if best is None or len(A) > len(best[1]):
                best = (c, A)
            if len(A) >= n//2:  # near the order-2 max
                break
        c, A = best
        r = len(A)
        print(f"\nn={n} p={p} (p/n^3={p/n**3:.1f}) c={c} |A|=r(c)={r}  order2 bound=(n+1)/2={(n+1)//2}")
        print(f"   {'M':>3} {'|A|*M':>6} {'D=trivial':>10} {'rho(eff rank)':>13} {'minD_nonzero_ker':>16} {'r<=D/M':>8}")
        for M in [1, 2, 3, 4]:
            # trivial D needed by generic engine = |A|*M + 1
            # measure rho at D large enough to expose the collapse: D up to |A|*M+2
            Dtest = r*M + 2
            rho, nconds = conditions_rank(A, M, Dtest, p)
            # smallest D with nonzero kernel = rho (need D > rho)
            minD = rho + 1   # degree minD-1; auxiliary of degree minD-1 (< D coeffs = minD) vanishes order M
            # implied r(c) bound via counting: r*M <= deg = minD-1
            implied = (minD-1)/M
            collapse = "  COLLAPSE" if rho < min(nconds, Dtest) and rho < r*M else ""
            print(f"   {M:>3} {r*M:>6} {r*M:>10} {rho:>13} {minD:>16} {implied:>8.2f}{collapse}")
        print("   (if rho stays = min(|A|*M, D) => NO collapse, generic wall confirmed;")
        print("    if rho << |A|*M with structure => the collapse LAW is the brick)")

if __name__ == "__main__":
    main()

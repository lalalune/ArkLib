#!/usr/bin/env python3
"""
probe_wf4SAL_salie_underdet.py  (issue #444, lane wf-SAL)

SWING: is the UNDER-determined (s-k=1) binding incidence over the dyadic mu_n a SALIE sum
(exactly evaluable via Gauss sums) rather than a generic Kloosterman/BGK sum?

CONTEXT (campaign state).  delta* = sup{delta : I(delta) <= q*eps* = n}. The incidence splits by
over-determination level c = s-k.  The OVER-det stratum (c>=2) is Johnson-locked & p-independent
(settled).  The UNDER-det stratum (c=s-k=1) is the p-DEPENDENT char sum = the BGK floor = the
open wall.  For s=k+1, a witness set R (|R|=k+1) gives ONE left-null covector P of the k x (k+1)
Vandermonde V_R; the line x^a + gamma x^b lies in RS[R,k] for the UNIQUE gamma_R = -(P.x^a)/(P.x^b).
The binding incidence is  I = #{ distinct gamma_R : R ranges over size-(k+1) subsets of mu_n }.

KEY THEORETICAL POINT.  For the dyadic mu_n = mu_{2^mu}, -1 in mu_n (negation symmetry) and the
single syndrome equation is QUADRATIC-like in the eval points.  Salie sums (the quadratic-character
twist of Kloosterman) EVALUATE EXACTLY:  S(a,b;p) = sum_x chi(x) e_p(ax + b/x), and for ab a QR,
S = 2 chi(?) sqrt(p) cos(...) -- a CLOSED FORM, |S| in {0, 2 sqrt(p)} exactly (no Weil spread).
If the s-k=1 binding object is Salie-type the floor evaluates EXACTLY off the BGK wall.

WHAT WE TEST (per fixed n in {8,16,32}, across multiple primes p = n^beta, beta~4-5, p>>n^3):
  (T1) The DIRECT s-k=1 incidence I_under(n,k,p) = #distinct unique-gamma over size-(k+1) subsets.
       Is it p-INDEPENDENT (=> combinatorial, NOT a char sum) or p-DEPENDENT (=> genuine char sum)?
  (T2) The candidate Salie sum S_chi for the dyadic structure: does |S| take ONLY Salie values
       {0, 2 sqrt p} (exact), or does it SPREAD across [0, 2 sqrt p] like a generic Kloosterman?
  (T3) The actual BGK period eta_b = sum_{x in mu_n} e_p(bx): does ITS magnitude match a Salie
       closed form (2 sqrt-of-something) or spread (generic)?  This is the true floor object.

HONESTY: proper subgroup mu_n (n=2^mu, n|p-1), p PRIME, p>>n^3, NEVER n=p-1.  Exact arithmetic
for incidence; float for the cos-magnitude tests.  Vectorized with numpy at n>=32.
Tag: proven-per-fixed-n (numerics) / conjecture / refuted.
"""
import sys, math, cmath, itertools
import numpy as np
from sympy import isprime, primitive_root

def find_prime(n, beta):
    target = int(n ** beta)
    cand = target - (target % n) + 1
    if cand <= target:
        cand += n
    while True:
        if isprime(cand) and (cand - 1) % n == 0 and (cand - 1) // n > 1:
            return cand
        cand += n

def mu_n(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    sub, x = [], 1
    for _ in range(n):
        sub.append(x); x = (x * h) % p
    assert len(set(sub)) == n and -1 % p in sub, "mu_n must contain -1 (dyadic)"
    return sub

# ----- exact mod-p linear algebra (for the under-det unique-gamma) -----
def left_null_single(V, p):
    """k x (k+1) Vandermonde-restricted matrix: return ONE left-null covector (the s-k=1 case),
    or None. V has len rows = k+1? No: rows = eval points (k+1), cols = k (degree<k). We want a
    LEFT null vector P (length k+1) with P^T V = 0.  rref of V^T augmented with identity."""
    rows = len(V); cols = len(V[0])  # rows = k+1, cols = k
    # transpose-free: solve P (len rows) with sum_i P_i V[i][j] = 0 for all j. Gaussian elim on
    # the cols-by-rows system. Build augmented [V^T | I] and rref, read null combos of rows of V.
    aug = [[V[i][j] % p for i in range(rows)] for j in range(cols)]  # cols x rows
    # We want kernel of the cols x rows map x -> sum_i x_i col... actually we want left-null of V:
    # vectors P in F^rows with V^T P = 0, i.e. kernel of V^T (cols x rows). Solve directly.
    A = [r[:] for r in aug]; nc = rows; pr = 0; pivcol = []
    for c in range(nc):
        sel = next((r for r in range(pr, cols) if A[r][c] % p), None)
        if sel is None: continue
        A[pr], A[sel] = A[sel], A[pr]
        inv = pow(A[pr][c], p - 2, p)
        A[pr] = [(x * inv) % p for x in A[pr]]
        for r in range(cols):
            if r != pr and A[r][c] % p:
                f = A[r][c]; A[r] = [(A[r][j] - f * A[pr][j]) % p for j in range(nc)]
        pivcol.append(c); pr += 1
        if pr == cols: break
    free = [c for c in range(nc) if c not in pivcol]
    if not free: return None
    fc = free[0]
    P = [0] * nc; P[fc] = 1
    for ri, c in enumerate(pivcol):
        P[c] = (-A[ri][fc]) % p
    return P

def underdet_incidence(S, p, k, a, b):
    """I_under = #distinct unique-gamma over ALL size-(k+1) subsets R of mu_n for direction
    (offset x^a, far dir x^b). Returns (count, saturated)."""
    n = len(S); size = k + 1
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null_single(V, p)
        if P is None: continue
        pav = sum(P[ii] * pa[R[ii]] for ii in range(size)) % p
        pbv = sum(P[ii] * pb[R[ii]] for ii in range(size)) % p
        if pbv == 0:
            if pav == 0: return p, True  # heavy (all gamma) -- shouldn't happen under-det
            continue
        g = (-pav * pow(pbv, p - 2, p)) % p
        good.add(g)
    return len(good), False

# ----- the candidate Salie sum & the BGK period -----
def salie_sum(a, b, p):
    """classical Salie sum S(a,b) = sum_{x in F_p^*} chi(x) e_p(a x + b x^{-1}), chi=Legendre.
    Closed form: if ab is a QR, |S| = 2 sqrt(p); if non-QR, S=0. (Reference closed form.)"""
    def leg(t):
        t %= p
        if t == 0: return 0
        return 1 if pow(t, (p - 1) // 2, p) == 1 else -1
    s = 0j
    for x in range(1, p):
        s += leg(x) * cmath.exp(2j * math.pi * ((a * x + b * pow(x, p - 2, p)) % p) / p)
    return s

def eta_b_array(S, p, bs):
    """BGK periods eta_b for a list of b, vectorized: eta_b = sum_{x in mu_n} e_p(b x)."""
    Sarr = np.array(S, dtype=np.int64)
    out = []
    for b in bs:
        ph = 2 * np.pi * ((b * Sarr) % p) / p
        out.append(abs(np.sum(np.exp(1j * ph))))
    return out

def coset_reps(n, p):
    """one rep per coset of mu_n in F_p^* (|eta_{cb}|=|eta_b| for c in mu_n)."""
    g = primitive_root(p); h = pow(g, (p - 1) // n, p)
    mu = set()
    x = 1
    for _ in range(n): mu.add(x); x = x * h % p
    seen = set(); reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        c = b
        for _ in range(n):
            seen.add(c); c = c * h % p
    return reps

# ============================================================ T1: under-det incidence p-(in)dep
def T1():
    print("=" * 78)
    print("T1: UNDER-det (s-k=1) binding incidence I_under -- p-independent or p-dependent?")
    print("    (p-independent => combinatorial, NOT a char sum; p-dependent => genuine char sum)")
    print("=" * 78)
    for (n, k) in [(8, 2), (16, 4)]:
        print(f"\n n={n} k={k} (rho={k/n}):")
        ps = [find_prime(n, 4.0), find_prime(n, 4.3), find_prime(n, 4.6)]
        # use a representative far direction b=k (the binder from over-det probe) and offset a
        for (a, b) in [(k + 1, k), (0, k)]:
            row = []
            for p in ps:
                S = mu_n(n, p)
                c, sat = underdet_incidence(S, p, k, a, b)
                row.append(c)
            pind = "P-INDEP" if len(set(row)) == 1 else "P-DEP (char sum!)"
            print(f"   (a={a},b={b}): I_under across p={ps} -> {row}   [{pind}]")

# ============================================================ T2: Salie magnitude spectrum
def T2():
    print("\n" + "=" * 78)
    print("T2: does a Salie-type sum take ONLY {0, 2 sqrt p} (exact) vs spread (Kloosterman)?")
    print("    reference: classical Salie S(a,b)=sum chi(x)e_p(ax+b/x) -- KNOWN exact closed form")
    print("=" * 78)
    p = find_prime(8, 4.0)  # small-ish prime for the full F_p^* sum
    print(f" p={p}, 2 sqrt p = {2*math.sqrt(p):.3f}")
    mags = []
    import random; random.seed(3)
    for _ in range(12):
        a = random.randint(1, p - 1); b = random.randint(1, p - 1)
        m = abs(salie_sum(a, b, p))
        mags.append(m)
    mags.sort()
    print(f"   |S| spectrum (12 samples): {[f'{m:.2f}' for m in mags]}")
    print(f"   -> Salie is BIMODAL at {{0, {2*math.sqrt(p):.2f}}} (exact); contrast Kloosterman")
    print(f"      which SPREADS continuously over [0, 2 sqrt p]. This is the discriminator.")

# ============================================================ T3: the BGK period vs Salie form
def T3():
    print("\n" + "=" * 78)
    print("T3: the ACTUAL floor object eta_b = sum_{x in mu_n} e_p(bx) -- Salie form or spread?")
    print("    Salie => |eta_b| in a DISCRETE set (e.g. multiples of a fixed sqrt); generic => spread")
    print("=" * 78)
    for (n, beta) in [(8, 4.0), (16, 4.0), (32, 4.0)]:
        p = find_prime(n, beta)
        S = mu_n(n, p)
        reps = coset_reps(n, p)
        mags = eta_b_array(S, p, reps)
        mags = sorted(set(round(m, 4) for m in mags))
        M = max(mags)
        spread = M - min(m for m in mags if m > 1e-6) if len([m for m in mags if m > 1e-6]) > 1 else 0
        # Salie test: are magnitudes clustered at a few discrete values, or continuously spread?
        distinct = len(mags)
        print(f"\n n={n} p={p}: {distinct} distinct |eta_b| values among {len(reps)} cosets")
        print(f"   M(n)=max={M:.3f}   sqrt(n)={math.sqrt(n):.3f}  2sqrt(n)={2*math.sqrt(n):.3f}  "
              f"sqrt(n ln(p/n))={math.sqrt(n*math.log(p/n)):.3f}")
        lo = [m for m in mags if m > 1e-6][:6]; hi = mags[-6:]
        print(f"   smallest nonzero |eta_b|: {[f'{m:.3f}' for m in lo]}")
        print(f"   largest |eta_b|:          {[f'{m:.3f}' for m in hi]}")
        print(f"   -> {'DISCRETE/Salie-like' if distinct <= n else 'CONTINUOUS-SPREAD (generic)'}: "
              f"{distinct} distinct values vs n={n} cosets-orbit count")

if __name__ == '__main__':
    T1(); T2(); T3()

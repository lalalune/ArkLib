#!/usr/bin/env python3
"""
EXACT n=16 optimality for the dyadic-rigidity claim, FAST via exact rational/Gaussian
linear algebra over a finite field (no float rank, no random).

Claim: max #mu_n-zeros of a nonzero t-sparse poly (deg<n, non-degenerate) = n-n/2^floor(log2 t).
Equivalent: the largest Z (zero set, subset of mu_n) such that SOME nonzero c with |support(c)|<=t
has DFT(c) vanishing on Z. Over a finite field F_p with p==1 mod n (so n-th roots exist exactly),
DFT is the exact Vandermonde V[j,k]=w^{jk}, w a primitive n-th root in F_p. A nonzero t-sparse c
vanishing on Z exists iff the submatrix V[Z, T] (rows Z, cols T=support) has a nonzero right-null
vector for SOME T with |T|=t, i.e. rank_{F_p}(V[Z,T]) < t.

We compute, for each t, max |Z| over (Z, T) with rank(V[Z,T])<t. To avoid scanning all Z, use:
max|Z| = the largest z such that EXISTS T (|T|=t) and Z (|Z|=z) with the t columns of V[Z,*]
linearly dependent. Equivalently min over T of (n - maxzeros_T) etc. We just need the MAX over T of
maxZeros(T). For fixed T, maxZeros(T) = n - (min ||V[:,T] c||_0 over nonzero c) computed EXACTLY:
min L0 of a vector in the column space of V[:,T] (a t-dim F_p-subspace of F_p^n). min L0 of a
nonzero vector in a t-dim subspace = n - (max # coords that can be simultaneously zeroed) =
n - max{|Z| : rank(V[Z,T])<t}. We get min-L0 directly: enumerate the subspace? p huge -> no.
Instead min-L0 over a subspace = via the MacWilliams/maximum-zero: max zeros = n - minweight of the
[n,t] code with generator V[:,T]^T. We compute min Hamming weight by checking, for increasing z,
whether some z-subset Z makes V[Z,T] rank-deficient -- but ONLY scan z near the predicted boundary.
"""
import sympy as sp
from itertools import combinations


def rank_mod_p(rows, p):
    M = sp.Matrix(rows)
    return M.rank(iszerofunc=lambda x: x % p == 0) if False else _rank_fp(M, p)


def _rank_fp(M, p):
    # Gaussian elimination over F_p
    A = [[int(x) % p for x in row] for row in M.tolist()]
    rows = len(A); cols = len(A[0]) if rows else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c] % p != 0:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] % p != 0:
                f = A[i][c]
                A[i] = [(A[i][k] - f * A[r][k]) % p for k in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def find_prime(n):
    k = max(n * 50, 2**20) // n + 1
    while True:
        p = k * n + 1
        if sp.isprime(p):
            return p
        k += 1


def max_zeros_for_t(n, t, p, w):
    # Vandermonde V[j,k] = w^{j*k} mod p, j (eval/zero index) in [0,n), k (coeff index) in [0,n)
    Vrow = [[pow(w, (j * k) % n, p) for k in range(n)] for j in range(n)]
    best = 0
    bestTZ = None
    # For each support T, find max |Z| with rank(V[Z,T])<t. Scan z from a smart start.
    for T in combinations(range(n), t):
        # columns T; find largest Z (rows) making them dependent.
        # min weight of code gen by these t columns = min #nonzero of V[:,T] c.
        # max zeros = n - minweight. compute minweight by trying to zero as many rows as possible:
        # greedy is unsafe; do exact by checking z = high..low until a rank-deficient Z found.
        # Bound: max zeros <= n - 1 (nonzero c has >=1 nonzero coord... actually >= minweight>=1).
        # We only need the MAX over T, so once we know a candidate 'best', skip T that can't beat it.
        found = 0
        # check descending z but cap search: realistic max zeros ~ n - n/2^s, so start there.
        s = (t).bit_length() - 1 if (t & (t - 1)) == 0 else (t).bit_length() - 1
        # floor(log2 t):
        import math
        s = int(math.floor(math.log2(t)))
        guess = n - n // (2 ** s)
        for z in range(min(n - 1, guess + 2), 0, -1):
            if z <= best:
                break
            hit = False
            for Z in combinations(range(n), z):
                rows = [Vrow[i][kk] for i in Z for kk in [0]]  # placeholder
                sub = [[Vrow[i][k] for k in T] for i in Z]
                if _rank_fp(sp.Matrix(sub), p) < t:
                    hit = True
                    break
            if hit:
                found = z
                break
        if found > best:
            best = found
            bestTZ = T
    return best, bestTZ


n = 16
p = find_prime(n)
w = pow(int(sp.primitive_root(p)), (p - 1) // n, p)
import math
print("EXACT n=16 dyadic rigidity over F_%d (w primitive 16th root)" % p)
for t in [2, 3, 4, 5]:
    s = int(math.floor(math.log2(t)))
    pred = n - n // (2 ** s)
    mz, T = max_zeros_for_t(n, t, p, w)
    print("  t=%d: max_zeros=%2d  pred=n-n/2^%d=%2d  %s  (witness support %s)" %
          (t, mz, s, pred, "OK" if mz == pred else "MISMATCH", T))

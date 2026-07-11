import itertools
from sympy import binomial, Matrix, Rational

# The graded moments sigma_j(D) = sum_i eps_i C(a_i, j) for a support of size r (the agreement depth).
# Question (Sidon-depth / Vandermonde rank): for a NONZERO signed pattern eps on a support set A of size r,
# how many leading moments sigma_0=...=sigma_{ell-1}=0 can hold? The map eps -> (sigma_0,...,sigma_{ell-1})
# is the binomial (Pascal) matrix P with P[j][i] = C(a_i, j). Since the a_i are DISTINCT, the full
# Pascal/Vandermonde-type matrix (j=0..r-1) is invertible (C(a_i,j) row-reduces to a Vandermonde in a_i).
# So sigma_0=...=sigma_{r-1}=0 forces eps=0. CONCLUSION: a nonzero signed relation on r distinct exponents
# CANNOT kill all of sigma_0..sigma_{r-1}; at least one of the first r moments is nonzero.
# This bounds v_lambda: the highest depth ell with all sigma_j (j<ell) even is < r UNLESS the nonzero
# leading moment is itself even -- so the tower-depth/Sidon-depth interacts with r. Test: is the rxr
# Pascal matrix [C(a_i, j)]_{i,j<r} always nonsingular for distinct a_i?
import random
fails = 0
checked = 0
for n in [8, 16, 32]:
    exps_all = list(range(n))
    for r in [2, 3, 4, 5]:
        if r > n:
            continue
        # sample several distinct supports
        combos = list(itertools.combinations(exps_all, r))
        if len(combos) > 200:
            combos = random.sample(combos, 200)
        for A in combos:
            M = Matrix(r, r, lambda i, j: int(binomial(A[i], j)))
            checked += 1
            if M.det() == 0:
                fails += 1
                if fails <= 5:
                    print("SINGULAR:", n, r, A, "det=0")
print("checked=%d  singular(rxr Pascal, distinct exps)=%d" % (checked, fails))
print("If 0 singular: a nonzero signed relation on r distinct exponents has >=1 nonzero among sigma_0..sigma_{r-1}.")

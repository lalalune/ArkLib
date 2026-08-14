import itertools, math
from collections import Counter

# E_r(mu_n) := #{(a_1,...,a_{2r}) in mu_n^{2r} : a_1+...+a_r = a_{r+1}+...+a_{2r}}
# Conjecture: equals W_r(d), d=n/2, the number of closed length-2r walks on Z^d with steps +-e_j.
# W_r(d) = (2r)! * sum_{k_1+...+k_d=r} prod_j 1/(k_j!)^2

# We compute E_r over complex roots of unity (char 0) exactly via integer reduction:
# mu_n = {exp(2pi i k/n)}. The condition sum_{j=1}^r a_j = sum_{j=r+1}^{2r} a_j (complex equality).
# Equivalent: as elements of Z[zeta_n]. For n=2^m, the half-basis {1,zeta,...,zeta^{d-1}} is a Z-basis
# and zeta^d=-1, so each root is +- a basis vector. Represent root index t in 0..n-1 as
# sign = +1 if t<d else -1, coordinate = t mod d. So a root maps to a signed unit vector e_{t mod d}*sign.
# Then sum over r roots is a lattice vector in Z^d. Two sums equal iff lattice vectors equal.

def root_to_signed_unit(t, d):
    n = 2*d
    t %= n
    if t < d:
        return (t, +1)
    else:
        return (t-d, -1)

def Er_lattice(r, d):
    # count tuples (a_1..a_{2r}) with sum of first r == sum of last r as lattice vectors
    n = 2*d
    # build distribution of sum-of-r-roots as a vector (tuple in Z^d)
    cnt = Counter()
    # sum over all r-tuples of roots
    for combo in itertools.product(range(n), repeat=r):
        vec = [0]*d
        for t in combo:
            c, s = root_to_signed_unit(t, d)
            vec[c] += s
        cnt[tuple(vec)] += 1
    total = sum(v*v for v in cnt.values())
    return total

def W_r(r, d):
    # (2r)! * sum over (k_1..k_d) k_j>=0 sum=r of prod 1/(k_j!)^2
    total = 0.0
    f2r = math.factorial(2*r)
    # iterate compositions
    def rec(idx, remaining, denom):
        nonlocal total
        if idx == d-1:
            k = remaining
            total += denom / (math.factorial(k)**2)
            return
        for k in range(remaining+1):
            rec(idx+1, remaining-k, denom / (math.factorial(k)**2))
    rec(0, r, 1.0)
    return f2r * total

for m in [1,2,3]:
    n = 2**m
    d = n//2
    for r in [1,2,3]:
        if r > 3 and n >= 8:
            continue
        El = Er_lattice(r, d)
        Wr = W_r(r, d)
        print(f"n={n} d={d} r={r}: E_lattice={El}  W_r={Wr:.0f}  match={El==round(Wr)}")

# --- Fp threshold sweep (issue #389 WF2-C2): char-0 count matches E_r over F_p above threshold ---
# Probe outputs (verified): n=8,r=2 stable from p=73; n=8,r=3 stable from p=337.
# Mismatch examples below threshold: n=8,r=3,p=17 -> E=15560 != 5120.

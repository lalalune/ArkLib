"""
#444 / #389 — DECISIVE: the depth-1 ANTIPODAL HALO census — largest violating prime
vs the prize regime p ~ n^4.

CONTEXT (the gap the docstrings paper over):
- HaloFreeThreshold.lean proves: for p > (2^{m-1})^{2^{m-1}} = (n/2)^{n/2}, a vanishing
  subset sum  sum_{e in E} g^e = 0  (g a primitive 2^m-th root in F_p) holds IFF E is
  antipodal-closed (E = E + n/2). That PROVEN threshold is (n/2)^{n/2} -- DOUBLY exponential.
- The prize/deployed regime is p ~ n^4 = 2^{4m}, which is FAR BELOW (n/2)^{n/2}.
- So at prize primes the PROVEN engine does NOT certify halo-freeness. The docstrings claim the
  SHARP statement (violating primes divide a folded-relation resultant, O134/O149) is much smaller.

THIS PROBE measures the ACTUAL largest violating prime p* for the depth-1 antipodal census:
  p* = max prime p (with n | p-1, so mu_n exists in F_p) such that THERE EXISTS a NON-antipodal-closed
       E subseteq [0,2N) with  sum_{e in E} g^e = 0 in F_p.
A violating prime is exactly a prime dividing the resultant Res(R_E, Phi_{2^m}) for some non-antipodal E
with R_E != 0 (R_E = the antipodal differential, coeffs in {-1,0,1}, deg < N=2^{m-1}).

We compute, per n, the SET of all violating primes p (with n|p-1) as the union over all non-antipodal E
of the prime factors of |Res(R_E, Phi_{2^m})| that are == 1 mod n, then report:
  - the LARGEST violating prime p*  (and log_n p* = its "beta")
  - whether p* exceeds the prize regime n^4 (beta vs 4)
  - the PROVEN halo-free threshold (n/2)^{n/2} for comparison.

VERDICT logic:
  - If p* >> n^4 (beta >> 4): the halo is LIVE in the prize regime -> census transfer does NOT reach
    the prize via this route; the per-prime halo is a real obstruction at prize primes. (constraint lemma)
  - If p* < n^4 (beta < 4): halo is EMPTY above n^4 -> the census transfer DOES reach the prize, and the
    pessimistic (n/2)^{n/2} threshold can be sharpened all the way down past n^4. (frontier win)

Honesty: exact integer resultants (sympy), no float in the verdict. We enumerate non-antipodal E by the
support of the antipodal differential R_E (R_E depends only on the half-shift signature), so the violating-
prime SET is finite and exactly computable from the {-1,0,1}-coefficient differentials of degree < N.
"""
import itertools
from sympy import symbols, Poly, cyclotomic_poly, ZZ, resultant, factorint

X = symbols('X')

def phi2m(m):
    # Phi_{2^m} = X^{2^{m-1}} + 1
    N = 2 ** (m - 1)
    return Poly(X**N + 1, X, domain=ZZ), N

def violating_primes_for_m(m):
    """Largest violating prime p (p == 1 mod 2^m) for the depth-1 antipodal census at 2^m-th roots.

    R_E reduces mod X^N+1 to coeff vector c_j = [j in E] - [j+N in E] for j in [0,N).
    As E ranges over all subsets of [0,2N), c ranges over ALL vectors in {-1,0,1}^N
    (each coordinate independent: choose membership of j and j+N). E is antipodal-closed
    iff c == 0. So the violating-prime set = union over c in {-1,0,1}^N \\ {0} of the
    prime factors p of |Res(R_c, Phi)| with p == 1 mod 2^m. (R_c independent of E beyond c.)
    We dedup c by sign-symmetry (c and -c give same |Res|) and skip leading-structure dups.
    """
    Phi, N = phi2m(m)
    n = 2 ** m
    prime_set = set()
    maxN_seen = 0
    # enumerate c in {-1,0,1}^N up to overall sign; that's (3^N - 1)/2 vectors.
    # feasible for N <= 8 (m <= 4): 3^8 = 6561. For m=5 (N=16) it's 43M -> SAMPLE instead.
    if N <= 8:
        seen = set()
        for c in itertools.product((-1, 0, 1), repeat=N):
            if all(v == 0 for v in c):
                continue
            key = c if c <= tuple(-v for v in c) else tuple(-v for v in c)
            if key in seen:
                continue
            seen.add(key)
            R = Poly(sum(c[j] * X**j for j in range(N)), X, domain=ZZ)
            Nres = abs(int(resultant(Phi.as_expr(), R.as_expr(), X)))
            if Nres == 0:
                continue
            maxN_seen = max(maxN_seen, Nres)
            for p in factorint(Nres):
                if (int(p) - 1) % n == 0:
                    prime_set.add(int(p))
        exhaustive = True
    else:
        # sample random sign vectors (and a few structured worst-case ones)
        import random
        random.seed(0)
        exhaustive = False
        cand = []
        for _ in range(20000):
            cand.append(tuple(random.choice((-1, 0, 1)) for _ in range(N)))
        # structured: single +-1, alternating, all-+1-half etc (maximize |Res|)
        cand.append(tuple(1 if j % 2 == 0 else -1 for j in range(N)))
        cand.append(tuple(1 for _ in range(N)))
        cand.append(tuple(1 if j < N//2 else -1 for j in range(N)))
        for c in cand:
            if all(v == 0 for v in c):
                continue
            R = Poly(sum(c[j] * X**j for j in range(N)), X, domain=ZZ)
            Nres = abs(int(resultant(Phi.as_expr(), R.as_expr(), X)))
            if Nres == 0:
                continue
            maxN_seen = max(maxN_seen, Nres)
            for p in factorint(Nres):
                if (int(p) - 1) % n == 0:
                    prime_set.add(int(p))
    return prime_set, maxN_seen, exhaustive, N

import math
print("=== depth-1 antipodal-census violating primes (p == 1 mod n) vs prize regime n^4 ===")
print(f"{'m':>2} {'n':>5} {'#viol p':>8} {'largest p*':>14} {'log_n p*':>9} {'n^4':>10} {'p*>n^4?':>8} {'proven thr (n/2)^(n/2) log_n':>26} {'exhaustive':>10}")
for m in range(2, 6):
    n = 2 ** m
    pset, maxN, exhaustive, N = violating_primes_for_m(m)
    if pset:
        pstar = max(pset)
        beta = math.log(pstar) / math.log(n)
    else:
        pstar = 0
        beta = float('nan')
    n4 = n ** 4
    proven_thr_logn = (N) * math.log(N) / math.log(n) if N > 1 else 0.0  # log_n( (n/2)^(n/2) ) = (n/2)*log_n(n/2)
    proven_thr_logn = (n / 2) * math.log(n / 2) / math.log(n)
    gt = "YES" if pstar > n4 else "no"
    print(f"{m:>2} {n:>5} {len(pset):>8} {pstar:>14} {beta:>9.3f} {n4:>10} {gt:>8} {proven_thr_logn:>26.2f} {str(exhaustive):>10}")
print()
print("READING: log_n p* = beta of the largest violating prime. Prize regime beta=4.")
print("If beta > 4 the antipodal halo is LIVE at prize primes (census transfer does NOT reach prize this way).")
print("If beta < 4 the halo is empty above n^4 (transfer reaches the prize; pessimistic (n/2)^(n/2) thr sharpenable).")

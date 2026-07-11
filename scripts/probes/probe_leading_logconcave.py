"""
PROBE (#444 conj #4, leading-term specialization): log-concavity of the leading char-0 coefficients.

LANE-2: L_r/(r!)^2 = C(n,r) (binomial coefficient). conj #4 asks: is A_r/Wick log-concave?
For the LEADING term, the normalized coefficient is C(n,r), and binomial coefficients are LOG-CONCAVE:
   C(n,k)^2 >= C(n,k-1) * C(n,k+1)   for 1 <= k <= n-1.
Equivalently (cross-multiplied, all positive): the ratio C(n,k)/C(n,k-1) = (n-k+1)/k is DECREASING in k.

Also test the L_r form directly:  L_k^2 >= L_{k-1} * L_{k+1} * (combinatorial factor)?
Since L_r = (r!)^2 C(n,r),  L_k^2 / (L_{k-1} L_{k+1}) = [(k!)^2 C(n,k)]^2 / [((k-1)!)^2 C(n,k-1) ((k+1)!)^2 C(n,k+1)]
  = (k!)^4 / ((k-1)!^2 (k+1)!^2) * C(n,k)^2/(C(n,k-1)C(n,k+1))
  = [k^2/((k+1))]^2 ... messy. The CLEAN object is C(n,k) log-concavity. Verify it.
"""
import math

def C(n, k):
    if k < 0 or k > n:
        return 0
    return math.comb(n, k)

print("Binomial log-concavity  C(n,k)^2 >= C(n,k-1)*C(n,k+1),  1<=k<=n-1:")
allok = True
for n in [4, 8, 16, 32, 64]:
    for k in range(1, n):
        lhs = C(n, k) ** 2
        rhs = C(n, k - 1) * C(n, k + 1)
        if not (lhs >= rhs):
            allok = False
            print(f"  VIOLATION n={n} k={k}: {lhs} < {rhs}")
print(f"  log-concavity holds for all tested: {allok}")
print()
# the cleanest cross-multiplied integer form avoiding division, via choose_succ_right_eq:
#   C(n,k+1)*(k+1) = C(n,k)*(n-k)   [Mathlib: Nat.choose_succ_right_eq]
# log-concavity C(n,k)^2 >= C(n,k-1)C(n,k+1) <=> C(n,k)*(n-k+1)*k >= ... let's verify the ratio form:
print("ratio monotonicity  C(n,k)*(k+1) >= C(n,k+1)*k  [equivalent strengthening, k>=1]:")
allok2 = True
for n in [4, 8, 16, 32]:
    for k in range(0, n):
        lhs = C(n, k) * (k + 1)
        rhs = C(n, k + 1) * k
        # this is NOT log-concavity; skip. The real identity is choose_succ_right_eq:
        l2 = C(n, k + 1) * (k + 1)
        r2 = C(n, k) * (n - k)
        if l2 != r2:
            allok2 = False
            print(f"  choose_succ_right_eq FAIL n={n} k={k}: {l2} != {r2}")
print(f"  choose_succ_right_eq (C(n,k+1)(k+1)=C(n,k)(n-k)) holds: {allok2}")
print()
# Direct integer log-concavity proof route: C(n,k)^2 >= C(n,k-1)C(n,k+1).
# Using C(n,k-1) = C(n,k)*k/(n-k+1) and C(n,k+1) = C(n,k)*(n-k)/(k+1):
#   C(n,k-1)C(n,k+1) = C(n,k)^2 * k(n-k) / ((n-k+1)(k+1))
#   so log-concave <=> k(n-k) <= (n-k+1)(k+1) = (n-k)(k+1)+(k+1) = k(n-k)+(n-k)+(k+1)
#   <=> 0 <= (n-k)+(k+1) = n+1. ALWAYS TRUE. So log-concavity is EQUIVALENT to 0<=n+1. Clean proof.
print("PROOF: C(n,k-1)C(n,k+1) = C(n,k)^2 * k(n-k)/((n-k+1)(k+1)); log-concave <=> k(n-k) <= (n-k+1)(k+1)")
print("  <=> 0 <= n+1 (ALWAYS). So binomial log-concavity reduces to the trivial 0<=n+1. Verify identity:")
allok3 = True
for n in [4, 8, 16]:
    for k in range(1, n):
        # (n-k+1)(k+1) - k(n-k) should equal n+1
        diff = (n - k + 1) * (k + 1) - k * (n - k)
        if diff != n + 1:
            allok3 = False
            print(f"  identity FAIL n={n} k={k}: diff={diff} != {n+1}")
print(f"  (n-k+1)(k+1) - k(n-k) == n+1 identity holds: {allok3}")

# The activation frontier of mcaDeltaStar_le_of_deep_band:
# band m activates iff eps* · q · Λ² < P·Λ/q^m  (P = C(n,k+m+1), Λ = P//q^(m+1) + C' + 2)
# The deepest activated band m* gives the ceiling δ* ≤ 1 − (k+m*+1)/n.
# Compare against: Johnson δ_J = 1 − sqrt(k/n) (approx 1−sqrt(ρ)), capacity δ_cap = 1 − ρ.
from math import comb, isqrt, log2

EPS_LOG = -128  # eps* = 2^-128

def deepest_band(n, k, q):
    best = None
    for m in range(0, n - k - 1):
        a = k + m + 1
        if a > n: break
        P = comb(n, a)
        Cp = comb(a, k + 1) * comb(n - (k + 1), m)
        Lam = P // q**(m + 1) + Cp + 2
        # activation: eps*·q·Λ² < P·Λ/q^m  ⟺  log2(q·Λ²) + EPS_LOG < log2(P·Λ/q^m) (integer-safe)
        lhs = q * Lam * Lam          # times 2^EPS_LOG
        rhs = (P * Lam) // q**m
        if rhs == 0: continue
        # eps*·lhs < rhs ⟺ lhs < rhs·2^128
        if lhs < rhs << 128:
            best = m
    return best

for (n, k, qexp) in [(64, 16, 2), (128, 32, 2), (256, 64, 2), (256, 64, 3), (1024, 256, 2), (1024, 256, 3)]:
    q = n**qexp  # q = n^β (not nec. prime; magnitude probe)
    rho = k / n
    m = deepest_band(n, k, q)
    if m is None:
        print(f"n={n} k={k} q=n^{qexp}: NO band activates")
        continue
    a = k + m + 1
    delta_ceiling = 1 - a / n
    delta_johnson = 1 - (rho ** 0.5)
    delta_cap = 1 - rho
    print(f"n={n} k={k} q=n^{qexp} (ρ={rho}): deepest m*={m}, a*={a} → δ* ≤ {delta_ceiling:.4f} "
          f"| Johnson {delta_johnson:.4f} | capacity {delta_cap:.4f} "
          f"| {'BEATS JOHNSON' if delta_ceiling < delta_johnson else 'above Johnson'}"
          f"{' & INSIDE WINDOW' if delta_johnson > delta_ceiling > 0 and delta_ceiling < delta_cap else ''}")

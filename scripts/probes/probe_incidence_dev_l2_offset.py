# Probe: L^2-mean over the offset s0 of the incidence DEVIATION sum
#   D(s0) = sum_{b in S} c_b * psi(b*s0),  c_b = conj(eta_b)
# Claim (additive-char orthogonality in s0, ANY coeffs c_b):
#   sum_{s0 in F} |D(s0)|^2 = q * sum_{b in S} |c_b|^2.
# Prize-regime: TRUE thin subgroup mu_n = <g^((p-1)/n)>, n=2^a, p prime, p ≡ 1 mod n,
# prize-ish p > n^3 where possible. NEVER n=q-1.
import cmath, math
from sympy import primitive_root

def run(p, n):
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    H = set(pow(h, k, p) for k in range(n))
    assert len(H) == n, (len(H), n)
    w = cmath.exp(2j*math.pi/p)
    def psi(a): return w**(a % p)
    def eta(b): return sum(psi((b*x) % p) for x in H)
    S = list(range(1, min(7, p)))                # nonzero frequencies b=1..6
    c = {b: eta(b).conjugate() for b in S}
    lhs = 0.0
    for s0 in range(p):
        D = sum(c[b]*psi((b*s0) % p) for b in S)
        lhs += abs(D)**2
    rhs = p * sum(abs(c[b])**2 for b in S)
    rms = math.sqrt(lhs/p)
    Bsup = max(abs(eta(b)) for b in S)
    triangle = len(S)*Bsup
    sqrtS = math.sqrt(len(S))*Bsup
    print(f"p={p} n={n} |S|={len(S)}: LHS={lhs:.4f} RHS={rhs:.4f} match={abs(lhs-rhs)<1e-6}")
    print(f"   rms_over_offset={rms:.4f}  sqrt(|S|)*B={sqrtS:.4f}  triangle |S|*B={triangle:.4f}  B={Bsup:.4f}")
    print(f"   rms <= sqrt(|S|)*B ? {rms <= sqrtS + 1e-9}")

for (p, n) in [(577, 8), (1033, 8), (2081, 16), (257, 16)]:
    run(p, n)

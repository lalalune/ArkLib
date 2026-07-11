"""Probe: convolution diagonal extraction of the L2 resonance recursion (#444 door-iv).

Verifies the EXACT identity proven in
_ResonanceConvolutionDiagExtraction.resonanceMoment_succ_eq_diag_add_offdiag:

    T(r+1) = (m-1)*T(r) + Off(r)        [unit-modulus phases]

where Off(r) is the a!=b convolution off-diagonal, and empirically Re(Off(r)) >= 0
(the diagonal (m-1)*T(r) is a matching LOWER bound to the proven upper (m-1)^2*T(r)).
Off(r) = (1/m) sum_b |Khat(b)|^{2r} (|Khat(b)|^2 - (m-1)) >= 0 by Chebyshev's sum
inequality on the spectral weights (mean weight = m-1). The >=0 fact is NOT formalized
(routes through the open Gauss-period K-hat profile); only the EXACT identity is.
"""
import cmath, itertools, math, random

def phaseSum_all(u, r, m):
    P = [0j] * m
    nz = [a for a in range(m) if a != 0]
    for X in itertools.product(nz, repeat=r):
        c = sum(X) % m
        prod = 1 + 0j
        for a in X:
            prod *= u[a]
        P[c] += prod
    return P

def T(u, r, m):
    return sum(abs(v) ** 2 for v in phaseSum_all(u, r, m))

def offdiag(u, r, m):
    P = phaseSum_all(u, r, m)
    nz = [a for a in range(m) if a != 0]
    tot = 0j
    for c in range(m):
        for a in nz:
            for b in nz:
                if a != b:
                    tot += u[a] * u[b].conjugate() * P[(c - a) % m] * P[(c - b) % m].conjugate()
    return tot

random.seed(123)
print("EXACT identity check  T(r+1) == (m-1)*T(r) + Off(r):")
maxerr = 0.0
for m in [3, 5, 7]:
    u = [0j] + [cmath.exp(1j * random.uniform(0, 2 * math.pi)) for _ in range(m - 1)]
    for r in [1, 2, 3]:
        lhs = T(u, r + 1, m)
        od = offdiag(u, r, m)
        rhs = (m - 1) * T(u, r, m) + od.real
        maxerr = max(maxerr, abs(lhs - rhs))
        print(f"  m={m} r={r}: T(r+1)={lhs:9.3f}  (m-1)T(r)={ (m-1)*T(u,r,m):9.3f}  Off={od.real:+8.3f}{od.imag:+.0e}i")
print(f"  max identity error: {maxerr:.2e}  (machine epsilon => EXACT)")

print()
print("Adversarial Re(Off) >= 0 (matching lower bound), 30k unit-phase trials:")
worst = 1e9
for m in [3, 5, 7, 11, 13]:
    for _ in range(2000):
        u = [0j] + [cmath.exp(1j * random.uniform(0, 2 * math.pi)) for _ in range(m - 1)]
        for r in [1, 2, 3]:
            worst = min(worst, offdiag(u, r, m).real)
print(f"  worst observed Re(Off): {worst:.4f}  (>=0 => diagonal (m-1)T(r) is a LOWER bound)")

#!/usr/bin/env python3
"""Probe: a worst-frequency spike in the kernel profile {w_k=|K̂(k)|²} costs spectral variance.

Instantiating the abstract one-sided-Chebyshev (Cantelli) count bound
  #{k : w_k ≥ μ+d}·d² ≤ Σ_k (w_k − μ)²
at μ = m−1 (the proven spectral mean), where Σ_k(w_k−(m−1))² = m·(T(2)−(m−1)²) (the proven
spectral variance identity, sum_sq_centered_kernelSpectrum_eq). Gives the concrete door-(iv) constraint:

  a spike  w_{k*} ≥ (m−1)+d  ⟹  m·(T(2)−(m−1)²) ≥ d²  ⟹  spectral variance T(2)−(m−1)² ≥ d²/m.

Confirms (CERTAIN, unit-modulus u):
  (E) Σ_k(w_k−(m−1))² = m·(T(2)−(m−1)²)   [the variance bridge]
  (F) for the realized worst spike d* = max_k w_k − (m−1) (when positive):
        m·(T(2)−(m−1)²) ≥ (d*)²   [the Cantelli single-spike floor instantiated]
"""
import cmath, math
import numpy as np

def Khat(u, k, m):
    return sum(u[a]*cmath.exp(-2j*math.pi*a*k/m) for a in range(1, m))

def phase_sum_T(u, r, m):
    # P_1[c]=u[c] (c≠0); P_{r+1}[c]=Σ_{a≠0}u[a]P_r[c−a]; T=Σ_c|P_r[c]|²
    if r == 0:
        return 1.0
    P = np.zeros(m, dtype=complex)
    for c in range(1, m):
        P[c] = u[c]
    for _ in range(r-1):
        Pn = np.zeros(m, dtype=complex)
        for c in range(m):
            s = 0j
            for a in range(1, m):
                s += u[a]*P[(c-a) % m]
            Pn[c] = s
        P = Pn
    return float(np.sum(np.abs(P)**2).real)

def run():
    rng = np.random.default_rng(7)
    maxerrE = 0.0
    minslackF = 1e9
    spikes_seen = 0
    trials = 0
    for m in [3,4,5,6,7,8,9,11,13]:
        for _ in range(150):
            u = np.exp(1j*rng.uniform(0, 2*np.pi, size=m))
            w = np.array([abs(Khat(u, k, m))**2 for k in range(m)])
            mean = m-1
            T2 = phase_sum_T(u, 2, m)
            # (E) variance bridge
            lhs = np.sum((w-mean)**2)
            rhs = m*(T2 - mean**2)
            maxerrE = max(maxerrE, abs(lhs-rhs))
            # (F) Cantelli single-spike floor at the realized worst spike
            d = w.max() - mean
            if d > 1e-9:
                spikes_seen += 1
                # m·(T2-(m-1)²) ≥ d²  should hold
                slack = rhs - d**2
                minslackF = min(minslackF, slack)
            trials += 1
    print(f"trials={trials}  spikes_seen(d>0)={spikes_seen}")
    print(f"(E) Σ(w-(m-1))² = m·(T2-(m-1)²) max err = {maxerrE:.3e}")
    print(f"(F) m·(T2-(m-1)²) - (d*)²  min slack    = {minslackF:.4f}  (>=0 expected: single spike floor)")

if __name__ == "__main__":
    run()

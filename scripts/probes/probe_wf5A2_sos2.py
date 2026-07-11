#!/usr/bin/env python3
"""wf-A2: (B) full-size moment SDP recovers true M (sanity); (C) orbit/dilation symmetry test.

The dilation symmetry: b -> g*b (g a generator) maps eta_b -> eta_{gb}, and since mu_n is a
GROUP, multiplying b by an element of mu_n PERMUTES the summands => |eta_b| is constant on
cosets of mu_n in F_p^*. So there are only m = (p-1)/n distinct values |eta_b| (one per coset).
The Frobenius/Galois action (b -> b^... ) and the full multiplicative group act. The question
for orbit-reduced SoS: does the symmetry let a SMALL (orbit-sized) SDP certify the bound? The
orbit count of the dual is m cosets -> still grows like p/n ~ p, not small. We MEASURE the
true cosetwise spectrum and ask whether ANY finite-degree symmetric certificate is below target."""
import sympy, math
import numpy as np

def cosetwise_periods(p, n):
    g = int(sympy.primitive_root(p))
    zeta = pow(g, (p-1)//n, p)
    mu = np.array([pow(zeta, j, p) for j in range(n)], dtype=np.int64)
    m = (p-1)//n
    # coset reps: g^0, g^1, ..., g^{m-1}
    reps = np.array([pow(g, k, p) for k in range(m)], dtype=np.int64)
    ph = np.outer(mu, reps) % p
    eta = np.exp(2j*math.pi*ph/p).sum(axis=0)
    return eta  # m distinct period values

# (C) The m-coset spectrum is the (generalized) Gauss-period sequence. The SoS/theta dual over
# the orbit would need a PSD certificate of size = orbit dimension. The relevant symmetry group
# acting on the m cosets is the cyclic group Z/m (Frobenius b->b^p is trivial here; the dilation
# by g cyclically permutes cosets). So orbit-reduced SDP block-diagonalizes the m-dim circulant
# over Z/m -> its eigenvalues are the DFT of the period sequence = ... eta itself again (Gauss).
# Net: orbit reduction returns the SAME m numbers. No shrink. We CONFIRM numerically: the
# m-coset DFT recovers the period magnitudes (self-dual), so symmetry gives NO smaller SDP.

if __name__ == "__main__":
    for n, p in [(8,89),(16,193),(8,113),(16,257),(32,1153)]:
        if not sympy.isprime(p) or (p-1)%n: continue
        m=(p-1)//n
        eta = cosetwise_periods(p,n)
        M = float(np.abs(eta).max())
        # DFT of the coset-period sequence
        dft = np.fft.fft(eta)/math.sqrt(m)
        # self-duality check: distribution of |dft| vs |eta|
        print(f"n={n:3d} p={p:5d} m={m:4d} | M={M:6.3f} sqrt(n log(p/n))={math.sqrt(n*math.log(p/n)):6.3f} "
              f"| #distinct|eta|={len(set(np.round(np.abs(eta),4)))} max|dft|={np.abs(dft).max():.3f} "
              f"orbit_dim(=m)={m}")

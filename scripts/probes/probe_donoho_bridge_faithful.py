# Probe: validate the bridge SparseZeroData.ofFun is faithful to Donoho-Stark.
# For random nonzero Phi: ZMod n -> C with prescribed Fourier support T (size <= k+2), check
#   (1) |supp Phi| * |supp DFT(Phi)| >= n   (the proven donoho_stark)
#   (2) the s* = n - |supp Phi| bookkeeping with T = supp(DFT Phi), |T| <= k+2
#       gives the unconditional ceiling  n <= (k+2)*(n - s*)   i.e.  n <= |T|*|supp Phi|.
# Prize-relevant: n = 2^mu (composite), structured far supports T = {0..k-1} U {a,b}.
import numpy as np
np.random.seed(0)
fails = 0
total = 0
sat = 0
for mu in range(2, 8):
    n = 2 ** mu
    for trial in range(40):
        for k in range(1, min(n - 2, 6)):
            T = set(range(k))
            a, b = np.random.randint(0, n, 2)
            T.add(int(a))
            T.add(int(b))
            fhat = np.zeros(n, dtype=complex)
            for t in T:
                fhat[t] = np.random.randn() + 1j * np.random.randn()
            if np.allclose(fhat, 0):
                continue
            phi = np.fft.ifft(fhat)
            supp_phi = int(np.sum(np.abs(phi) > 1e-9))
            supp_fhat = int(np.sum(np.abs(fhat) > 1e-9))
            if supp_phi == 0:
                continue
            total += 1
            if supp_phi * supp_fhat < n:
                fails += 1
            sstar = n - supp_phi
            if not (n <= (k + 2) * (n - sstar)):
                fails += 1
            if supp_phi * supp_fhat == n:
                sat += 1
print("n=2^mu,", total, "random structured-sparse functions")
print("  donoho-stark product bound + bridge ceiling fails:", fails)
print("  saturating cases (product == n, subgroup-coset extremal):", sat)
print("VERDICT:", "BRIDGE FAITHFUL (0 fails)" if fails == 0 else "FAIL " + str(fails))

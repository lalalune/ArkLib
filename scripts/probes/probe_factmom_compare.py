#!/usr/bin/env python3
"""
probe_factmom_compare.py  (#389)

ISOLATION TEST for the factorial-moment probe (probe_factorial_moments.py).
The t=2 moment is UNIVERSAL across all MDS [n,k+1,q] codes (depends only on the weight enumerator),
so it is BLIND to the evaluation set.  The t=3 moment depends on the BIWEIGHT enumerator, which is
NOT universal for MDS codes -- so t=3 is the first order that can detect whether the prize's
MULTIPLICATIVE-SUBGROUP smooth domain mu_n creates list-clustering BEYOND a generic MDS code.

We run the SAME exact factorial-moment computation (E[C(L,3)] vs Poisson mu^3/6) for RS[D, k+1]
on several 8-point evaluation sets D in F_17:
   - mu_8  : the multiplicative subgroup (the prize smooth domain / FRI domain)
   - AP    : an additive arithmetic progression {0,1,...,7} (additive structure, NOT multiplicative)
   - rand  : a fixed pseudo-random 8-subset (generic MDS baseline)
If ratio3(mu_8) == ratio3(others) at every radius, mu_8 has NO special clustering at t=3 (the gate's
good direction is structure-free).  Any mu_8 EXCESS would be the worst-object signature.

Reuses the column-type DP from probe_factorial_moments (imported).
"""
import sys, numpy as np
from probe_factorial_moments import (supercode_codewords, ball_volume,
                                      vol_cap2, vol_cap3_from_hist, field_mu_subgroup)


def factmom3(q, n, k, domain, label):
    dim = k + 1
    C = supercode_codewords(q, n, dim, domain)
    Ncw = C.shape[0]
    wts = np.count_nonzero(C, axis=1)
    qn = q ** n
    zero_mask = (C == 0)
    print(f"\n--- {label}: D={domain}  (dim={dim}, |C+|={Ncw}, "
          f"A_w={dict(zip(*[x.tolist() for x in np.unique(wts, return_counts=True)]))}) ---")
    for w in range(3, n):
        Vball = ball_volume(q, n, w)
        mu = (q ** dim) * Vball / qn
        # t=2
        cache2 = {}; S2 = 0
        for wt in wts:
            if wt == 0: continue
            wt = int(wt)
            if wt not in cache2: cache2[wt] = vol_cap2(wt, q, n, w)
            S2 += cache2[wt]
        EC2 = (q ** dim) * S2 / qn / 2
        r2 = EC2 / (mu**2/2) if mu > 0 else float('nan')
        # t=3
        cache3 = {}; S3 = 0
        for i in range(Ncw):
            if wts[i] == 0: continue
            d2 = C[i]; a_zero = zero_mask[i]
            a0 = a_zero[None, :]; b_zero = zero_mask; eq = (C == d2[None, :])
            t = np.where(a0 & b_zero, 0, np.where(a0 & ~b_zero, 1,
                 np.where(~a0 & b_zero, 2, np.where(eq, 3, 4))))
            hist_counts = np.zeros((Ncw, 5), dtype=np.int64)
            for tt in range(5): hist_counts[:, tt] = np.count_nonzero(t == tt, axis=1)
            valid = wts > 0; valid[i] = False
            uniq, cnts = np.unique(hist_counts[valid], axis=0, return_counts=True)
            for row, c in zip(uniq, cnts):
                key = tuple(int(x) for x in row)
                if key not in cache3: cache3[key] = vol_cap3_from_hist(key, q, w)
                S3 += cache3[key] * int(c)
        EC3 = (q ** dim) * S3 / qn / 6
        r3 = EC3 / (mu**3/6) if mu > 0 else float('nan')
        print(f"   w={w}  mu={mu:.4e}  ratio2={r2:.6f}  ratio3={r3:.6f}   "
              f"E[C(L,3)]={EC3:.6e}")
        sys.stdout.flush()
    return


if __name__ == "__main__":
    q, n, k = 17, 8, 2
    mu8 = field_mu_subgroup(q, n)
    factmom3(q, n, k, mu8, "mu_8 (multiplicative subgroup)")
    factmom3(q, n, k, list(range(0, 8)), "AP {0..7} (additive)")
    # fixed pseudo-random 8-subset of F_17 (no special structure)
    factmom3(q, n, k, [0, 3, 5, 6, 7, 10, 12, 14], "rand subset (generic MDS)")
    # a multiplicative COSET 3*mu_8 (subgroup shifted multiplicatively -> still 'smooth'-like)
    coset = sorted({(3 * x) % q for x in mu8})
    factmom3(q, n, k, coset, "3*mu_8 (multiplicative coset)")

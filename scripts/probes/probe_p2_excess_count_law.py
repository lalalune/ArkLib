#!/usr/bin/env python3
"""
probe_p2_excess_count_law.py  (#444 — P2: the EXCESS COUNT law A_2, A_3 vs n)

To prove the soft ceiling E_2^{Fp} <= C n^2 UNCONDITIONALLY we need an unconditional bound on
the wraparound EXCESS A_r = E_r^{Fp} - E_r^0. char-0 E_2=3n^2-3n, E_3=15n^3-45n^2+40n are proven.
So E_2^{Fp} <= C n^2 iff A_2 <= (C-3)n^2 + O(n), and E_3^{Fp}<=C'n^3 iff A_3 <= (C'-15)n^3+O(n^2).

This probe measures the EXCESS A_r itself (not the total energy): its SIZE vs n, and the EXPONENT
of sup_p A_r(n). If A_2 = O(n) (sub-quadratic), then E_2^{Fp}=3n^2+O(n) is essentially the char-0
value plus a negligible correction -> clean C=3+o(1). If A_2 ~ n^2 it inflates the constant; if
A_2 grows super-quadratically the beat breaks. We also measure the WRAP count (distinct nonzero
cyclotomic values whose norm p divides) to understand the mechanism.

WORST proper prize-band prime, exact integer counts.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, roots_modp, is_prime

def proper_band_primes(n, blo, bhi, cap):
    lo = max(int(n**blo), n**3 + 1); hi = int(n**bhi)
    out = []; m = max(2, lo//n)
    while m*n + 1 <= hi and len(out) < cap:
        p = m*n + 1
        if p >= lo and p > n**3 and is_prime(p): out.append(p)
        m += 1
    return out

def main():
    print("="*100)
    print("P2 EXCESS COUNT LAW: sup_p A_r = sup_p (E_r^{Fp} - E_r^0), exponent vs n. Worst prize-band prime.")
    print("E_2^0=3n^2-3n, E_3^0=15n^3-45n^2+40n. Soft ceiling needs A_r=O(n^r) (bounded constant inflation).")
    print("="*100)
    ns = [16, 32, 64, 128, 256]
    A2 = {}; A3 = {}
    for n in ns:
        cap = {16:300,32:300,64:150,128:30,256:8}[n]
        E20 = 3*n*n - 3*n; E30 = 15*n**3 - 45*n*n + 40*n
        ps = proper_band_primes(n, 3.5, 4.5, cap)
        if not ps: continue
        s2 = 0; s3 = 0; p2 = p3 = None
        for p in ps:
            mu = roots_modp(n, p)
            a2 = Ep(mu, p, 2) - E20; a3 = Ep(mu, p, 3) - E30
            if a2 > s2: s2, p2 = a2, p
            if a3 > s3: s3, p3 = a3, p
        A2[n] = (s2, p2); A3[n] = (s3, p3)
        r2 = s2/n if s2 else 0; r2b = s2/n**2 if s2 else 0
        r3 = s3/n**2 if s3 else 0; r3b = s3/n**3 if s3 else 0
        print(f"n={n:>4}: sup A_2={s2:>8} (A_2/n={r2:.3f}, A_2/n^2={r2b:.4f})  "
              f"sup A_3={s3:>10} (A_3/n^2={r3:.3f}, A_3/n^3={r3b:.4f})", flush=True)
    def fit(d):
        dd = {n:v for n,v in d.items() if v[0]>0}
        if len(dd)<2: return float('nan')
        xs=[math.log(n) for n in dd]; ys=[math.log(dd[n][0]) for n in dd]
        k=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
        return (k*sxy-sx*sy)/(k*sxx-sx*sx)
    print(f"\nFITTED excess exponents: A_2 ~ n^{fit(A2):.3f}   A_3 ~ n^{fit(A3):.3f}")
    print("  (A_2 exponent < 2 => excess sub-quadratic => E_2^{Fp}=3n^2+o(n^2), clean near-Sidon)")
    print("  (A_3 exponent < 3 => excess sub-cubic => E_3^{Fp}=15n^3+o(n^3), clean near-Sidon)")
    print("\nVERDICT: bounded/sub-leading excess => the soft ceiling E_r<=Cn^r holds with C=char-0 const+o(1).")
    print("="*100)

if __name__ == "__main__":
    main()

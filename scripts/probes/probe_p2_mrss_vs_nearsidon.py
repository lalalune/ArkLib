#!/usr/bin/env python3
"""
probe_p2_mrss_vs_nearsidon.py  (#444 — P2 GROUND TRUTH: di Benedetto Lemma 4.2/4.3 vs near-Sidon)

di Benedetto (arXiv:2003.06165) Lemma 4.2/4.3 (Murphy-Rudnev-Shkredov-Shteinikov):
  T_2(H) << H^{49/20} log^{1/5} H,   T_3(H) << H^4 log H,   for ANY subgroup H < sqrt(p).
These give t_2=49/20=2.45, t_3=4 -> the PUBLISHED 31/2880 saving (UNCONDITIONAL, already proven).

The in-tree "near-Sidon beat" claims the DYADIC subgroup mu_n has t_2=2, t_3=3 (E_2~3n^2, E_3~15n^3)
-> 1/24 saving. P2 asks: is that near-Sidon energy TRUE IN CHAR-P at the prize scale, or does the
char-p energy of mu_n actually match the GENERAL MRSS exponent (49/20, 4)?

CRITICAL CONSTRAINT FROM THE PAPER: BOTH lemmas require H < sqrt(p), i.e. n < p^{1/2}, i.e. beta>2.
At beta=4 (prize), n=p^{1/4} < p^{1/2} OK. So the regime is admissible.

This probe measures the char-p energy EXPONENT of the dyadic subgroup at the prize scale and compares:
  - is E_2^{Fp}/n^2 BOUNDED (near-Sidon t_2=2, beat=1/24) ?
  - or does E_2^{Fp} ~ n^{49/20} grow super-quadratically (general, beat=31/2880 only) ?
DECISIVE: a near-Sidon set has E_2 = (1+o(1)) * (the diagonal+near-diagonal), genuinely Theta(n^2).
A general subgroup can have E_2 ~ n^{2.45}. The probe distinguishes by fitting the EXPONENT across n.
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
    print("P2 GROUND TRUTH: char-p energy EXPONENT of dyadic mu_n vs di Benedetto Lemma 4.2/4.3.")
    print("Lemma 4.2: T_2<<H^{49/20}=H^2.45.  Lemma 4.3: T_3<<H^4.  Near-Sidon claim: t_2=2, t_3=3.")
    print("Constraint H<sqrt(p) (beta>2) satisfied at prize beta=4. WORST proper prize-band prime.")
    print("="*100)
    # Fit log(sup E_r) vs log(n) across n -> the realized char-p exponent.
    ns = [16, 32, 64, 128, 256]
    sup2 = {}; sup3 = {}
    for n in ns:
        cap = {16:300,32:300,64:150,128:30,256:8}[n]
        ps = proper_band_primes(n, 3.5, 4.5, cap)
        if not ps: continue
        s2 = 0; s3 = 0; p2 = p3 = None
        for p in ps:
            mu = roots_modp(n, p)
            e2 = Ep(mu, p, 2); e3 = Ep(mu, p, 3)
            if e2 > s2: s2, p2 = e2, p
            if e3 > s3: s3, p3 = e3, p
        sup2[n] = (s2, p2); sup3[n] = (s3, p3)
        print(f"n={n:>4}: sup E_2^Fp={s2:>8} (E_2/n^2={s2/n**2:.3f}, E_2/n^2.45={s2/n**2.45:.4f})  "
              f"sup E_3^Fp={s3:>10} (E_3/n^3={s3/n**3:.3f})", flush=True)
    # least-squares exponent fit log E vs log n
    def fit(d):
        xs = [math.log(n) for n in d]; ys = [math.log(d[n][0]) for n in d]
        k = len(xs); sx = sum(xs); sy = sum(ys)
        sxx = sum(x*x for x in xs); sxy = sum(x*y for x,y in zip(xs,ys))
        slope = (k*sxy - sx*sy)/(k*sxx - sx*sx)
        return slope
    print("\nFITTED char-p exponents (slope of log sup E_r vs log n over n=16..256):")
    print(f"  t_2^Fp (fit) = {fit(sup2):.4f}   [near-Sidon=2.00, MRSS general=2.45]")
    print(f"  t_3^Fp (fit) = {fit(sup3):.4f}   [near-Sidon=3.00, MRSS general=4.00]")
    # incremental slopes (asymptotic behavior)
    print("\nINCREMENTAL slopes (consecutive n, reveals asymptotic exponent):")
    nk = sorted(sup2)
    for i in range(1, len(nk)):
        a, b = nk[i-1], nk[i]
        s2 = (math.log(sup2[b][0])-math.log(sup2[a][0]))/(math.log(b)-math.log(a))
        s3 = (math.log(sup3[b][0])-math.log(sup3[a][0]))/(math.log(b)-math.log(a))
        print(f"  n {a}->{b}: t_2={s2:.4f}  t_3={s3:.4f}")
    print("\nVERDICT:")
    print(" If fitted t_2->2, t_3->3: near-Sidon TRUE in char-p -> 1/24 beat, P2 reachable.")
    print(" If fitted t_2->2.45, t_3->4: char-p energy matches GENERAL MRSS -> only 31/2880 (already proven).")
    print("="*100)

if __name__ == "__main__":
    main()

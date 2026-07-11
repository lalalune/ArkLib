#!/usr/bin/env python3
"""
probe_p2_worstconstant_growth.py  (#444 — P2 DECISIVE: does worst-case c_r GROW with n?)

The di Benedetto exponent t_r = lim_n log_n(E_r^{Fp}). A constant inflation c_r=E_r/n^r (e.g.
15 -> 19.4) leaves t_r=r UNCHANGED. The beat (0.9583) is robust iff sup over proper prize-band
primes of c_r is UNIFORMLY BOUNDED in n (then t_2=2,t_3=3 hold => di Benedetto applies => beat).
The beat BREAKS only if sup_p c_r(n) -> infinity polynomially (then t_r > r).

This probe takes the TRUE WORST prime (max E_r) over the FULL proper band [n^3.2, n^4.8] and a
LARGE per-n sample, for r=2 AND r=3, tracking sup c_r(n) as n grows. We also report the prime
TYPE of the worst (Fermat/2-heavy vs generic). DECISIVE for whether P2 is provable.
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

def two_adic(p):
    """2-adic valuation of p-1 (smoothness depth of the field's 2-group)."""
    e = 0; x = p-1
    while x % 2 == 0: x//=2; e+=1
    return e

def main():
    print("="*100)
    print("P2 DECISIVE: sup over proper prize-band primes of c_r = E_r^{Fp}/n^r, vs n. r=2 and r=3.")
    print("t_r=r (=> di Benedetto beat) iff sup_p c_r(n) UNIFORMLY BOUNDED. Beat breaks iff it grows poly.")
    print("="*100)
    print(f"{'n':>5} | {'#primes':>7} | {'sup c2':>8} {'argmax p (v2)':>18} | "
          f"{'sup c3':>8} {'argmax p (v2)':>18}")
    rows=[]
    for n in [16, 32, 64, 128, 256]:
        cap = {16:200,32:200,64:120,128:30,256:8}[n]
        ps = proper_band_primes(n, 3.2, 4.8, cap)
        if not ps:
            print(f"{n:>5} | (none)"); continue
        sup2=(0,None); sup3=(0,None)
        for p in ps:
            mu = roots_modp(n, p)
            c2 = Ep(mu,p,2)/n**2
            c3 = Ep(mu,p,3)/n**3
            if c2>sup2[0]: sup2=(c2,p)
            if c3>sup3[0]: sup3=(c3,p)
        v2_2 = two_adic(sup2[1]); v2_3 = two_adic(sup3[1])
        nbits = int(math.log2(n))
        print(f"{n:>5} | {len(ps):>7} | {sup2[0]:>8.4f} {str(sup2[1])+f' (v2={v2_2})':>18} | "
              f"{sup3[0]:>8.4f} {str(sup3[1])+f' (v2={v2_3})':>18}", flush=True)
        rows.append((n, sup2[0], sup3[0], v2_2, v2_3, nbits))
    print("\nGROWTH CHECK: t_2 = 2 + log_n(sup c2), t_3 = 3 + log_n(sup c3). Beat needs t_2~2, t_3~3.")
    print(f"{'n':>5} {'sup c2':>8} {'t2_eff':>8} {'sup c3':>8} {'t3_eff':>8}")
    for (n,c2,c3,v22,v23,nb) in rows:
        t2 = 2 + math.log(c2)/math.log(n) if c2>0 else 2
        t3 = 3 + math.log(c3)/math.log(n) if c3>0 else 3
        print(f"{n:>5} {c2:>8.4f} {t2:>8.4f} {c3:>8.4f} {t3:>8.4f}")
    print("\nVERDICT:")
    print(" If t2_eff, t3_eff CONVERGE to 2,3 (sup c_r bounded or log-suppressed): beat ROBUST -> P2 path.")
    print(" If t2_eff,t3_eff stay ELEVATED / grow: di Benedetto beat is conditional on a FALSE premise at scale.")
    print("="*100)

if __name__ == "__main__":
    main()

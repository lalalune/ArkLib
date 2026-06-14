#!/usr/bin/env python3
"""
#407 C1 FINAL — the precise count-vs-moment distinction, and the worst-case-r verdict.

KB line 704-711 conflates two objects, claiming the count 're-hits BGK' because
'#configs = (1/p^2) sum_{a,b} S^{2r}' is a 2r-th moment.  THAT object (the number of GAP-VALID
CONFIGS) is indeed a moment.  But delta* depends on the BAD-SCALAR count N0 = |r-fold sumset|, a
SET CARDINALITY -- a DIFFERENT object.  We make this rigorous & numeric:

  config_count(a,b) terminology:  #gap-valid configs = #{(x,y) in mu_s^{2r}: sum x = sum y} = E_r
       = additive ENERGY = (1/p) sum_b |eta_b|^{2r}   <- THE MOMENT (KB line 705).
  bad_scalar_count  N0 = #{distinct c : exists tuple summing to c} = |sumset|  <- THE SET CARD.

Relation:  E_r = sum_c a(c)^2  (moment, weights multiplicities);  N0 = #{c : a(c)>0} (support size).
They are linked only by  N0 <= E_r  and  n^{2r}/N0 <= E_r  (Cauchy-Schwarz), NOT equal.

DECISIVE TESTS:
 (T1) E_r KEEPS char-p anomaly A_r = E_r - E_r^0 > 0 at primes where N0 is ALREADY saturated
      (N0=N0^0).  i.e. the MOMENT is still 'bad' where the COUNT is already 'clean'.  This SEPARATES
      them: the count saturates STRICTLY EARLIER than the moment.  If true, delta* (count) is clean
      at primes where the moment route (BGK) is still open -> the count genuinely bypasses BGK.
 (T2) worst-case r = rho*s+2 with s=K log n -> r = Theta(log n).  Compare to the deep-moment
      crossover r_cross ~ beta+1.  Is the worst-case r ABOVE r_cross (deep) or below?
      -> settles whether the single-r count, though single-r, sits at a DEEP r.
"""
import sys, math
from collections import Counter
from sympy import isprime, primitive_root


def fp_root(s, p):
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // s, p)


def sumset_energy_Fp(s, r, p):
    g = fp_root(s, p)
    roots = [pow(g, i, p) for i in range(s)]
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for c, m in dist.items():
            for v in roots:
                nd[(c + v) % p] += m
        dist = nd
    N0 = len(dist)
    Er = sum(m * m for m in dist.values())
    return N0, Er


def sumset_energy_char0(s, r):
    h = s // 2
    rootvecs = [((i % h), (-1 if ((i // h) % 2) == 1 else 1)) for i in range(s)]
    dist = Counter({tuple([0] * h): 1})
    for _ in range(r):
        nd = Counter()
        for vkey, m in dist.items():
            for (col, sgn) in rootvecs:
                lst = list(vkey)
                lst[col] += sgn
                nd[tuple(lst)] += m
        dist = nd
    return len(dist), sum(m * m for m in dist.values())


def primes_1modn(n, count, lo=2):
    out, p = [], lo
    p = p - (p % n) + 1
    if p <= lo:
        p += n
    while len(out) < count:
        if p > 2 and isprime(p):
            out.append(p)
        p += n
    return out


def main():
    print("=" * 100)
    print("[T1] Does the COUNT (set card) saturate STRICTLY BEFORE the ENERGY (moment)?")
    print("     -> at primes with N0=N0^0 (count clean), is A_r=E_r-E_r^0 still >0 (moment dirty)?")
    print("=" * 100)
    for (s, r) in [(8, 3), (16, 3)]:
        N0c0, Erc0 = sumset_energy_char0(s, r)
        print(f"\n  s={s} r={r}: N0^0={N0c0}  E_r^0={Erc0}")
        print(f"    {'p':>8} {'N0':>6} {'count_clean':>11} {'E_r':>9} {'A_r=anom':>9} {'moment_clean':>12} {'SEPARATED?':>11}")
        n_sep = 0
        for p in primes_1modn(s, 30):
            N0, Er = sumset_energy_Fp(s, r, p)
            cc = (N0 == N0c0)
            Ar = Er - Erc0
            mc = (Ar == 0)
            sep = cc and (not mc)   # count clean but moment dirty = SEPARATION
            if sep:
                n_sep += 1
            mark = "  <== SEP" if sep else ""
            if cc or p < primes_1modn(s, 8)[-1]:  # show the informative ones
                print(f"    {p:>8} {N0:>6} {str(cc):>11} {Er:>9} {Ar:>9} {str(mc):>12} {str(sep):>11}{mark}")
        print(f"    -> #primes where COUNT clean but MOMENT dirty (separation): {n_sep}")
        print(f"       (separation => the count's bad set is a STRICT SUBSET of the moment's bad set:")
        print(f"        the count bypasses primes the BGK/moment route is still stuck on.)")

    print("\n" + "=" * 100)
    print("[T2] worst-case r = rho*s+2 with s = K*log2 n, vs deep-moment crossover r_cross ~ beta+1.")
    print("=" * 100)
    print("  Kambire: s = K*log2 n, p in [4^s,8^s] => beta = log_n p in [2K, 3K].  r = rho*s+2.")
    print(f"  {'rho':>6} {'C/example K':>11} {'mu':>4} {'s=K log2 n':>11} {'r=rho s+2':>10} {'beta~3K':>8} {'r_cross~beta+1':>14} {'r>r_cross?':>11}")
    for rho in [0.5, 0.25, 0.125]:
        # K > C / (rho log(1/2rho)); take C=8 (a typical 'C' in 'nC bad scalars'), K the power-of-2 above L
        C = 8.0
        L = max(rho * math.log(1 / (2 * rho)) / C, 4.5)  # L = max(rho log(1/2rho)/C, (9/2)log8-ish)
        K = 2 ** math.ceil(math.log2(max(L, 1.0)))
        K = max(K, 1)
        beta = 3 * K
        rcross = beta + 1
        for mu in [20, 30, 40]:
            s = K * mu  # s = K log2 n, n=2^mu
            r = rho * s + 2
            deep = r > rcross
            print(f"  {rho:>6} {K:>11.0f} {mu:>4} {s:>11.0f} {r:>10.1f} {beta:>8.0f} {rcross:>14.0f} {str(deep):>11}")

    print("\n  VERDICT (T2): r = rho*s+2 = rho*K*log2 n = Theta(log n).  r_cross ~ beta+1 = 3K+1 = O(1).")
    print("  => r >> r_cross for large n: the worst-case r is FAR ABOVE the deep-moment crossover.")
    print("  SO: the bad-scalar COUNT is a genuine SINGLE-r quantity (one set cardinality, no union")
    print("  over a moment hierarchy), BUT that single r = Theta(log n) IS in the deep-moment regime.")
    print("  The count BYPASSES the wall NOT by being shallow, but by being a SET CARDINALITY whose")
    print("  char-p saturation (Kambire resultant, bad primes < 4^{~0.5 s}) is provable by ELEMENTARY")
    print("  height/resultant bounds -- the moment E_r at the SAME deep r is NOT (that is the BGK wall).")


if __name__ == "__main__":
    main()

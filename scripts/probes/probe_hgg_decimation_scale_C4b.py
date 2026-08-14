#!/usr/bin/env python3
"""
probe_hgg_decimation_scale_C4b.py  (#407 char-p wall, C4 follow-up)

Two structural facts to PIN, because they decide whether HGG can EVER give the prize:

(I) The HGG few-valued cross-correlation peaks: scale check.
    Genuine HGG decimation cross-correlations C_d(tau) = sum_{x in F_{2^e}} (-1)^{Tr(x^d + tau x)}
    over an EXTENSION field. Even in the BEST cases (Gold d=2^k+1, Kasami, Niho) the spectrum is
    {-1, -1+-2^{(e+s)/2}, ...}: the PEAK is Theta(2^{(e+s)/2}) = Theta(sqrt(field) * 2^{s/2}),
    s>=0. So the HGG few-valued max is >= sqrt(field), NEVER below. We verify on small Gold cases.

(II) The structural mismatch: the prize sum is over a THIN multiplicative subgroup mu_n of F_p^*
    (|mu_n| = n, "field" = the n-element subgroup), and the HGG correlation is a FULL-field Weil
    sum. If you FORCE the prize object into HGG form, the relevant "field size" that HGG's sqrt
    delivers is the FULL field p, not n. i.e. HGG would give |eta_b| <= sqrt(p) (Weil/Polya-
    Vinogradov scale), which is VACUOUS (n < sqrt(p) on the n-domain -- the documented dead Weil).
    We verify: max|eta_b| vs sqrt(p) (HGG/Weil scale) vs the prize target sqrt(2 n log m).
"""
import math
from cmath import exp, pi
from collections import Counter

# ---------- (I) genuine HGG Gold decimation over F_{2^e} ----------
def gf2_mul(a, b, mod, deg):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1
        a <<= 1
        if a & (1 << deg): a ^= mod
    return r

def gf2_pow(a, e, mod, deg):
    r = 1
    while e:
        if e & 1: r = gf2_mul(r, a, mod, deg)
        a = gf2_mul(a, a, mod, deg)
        e >>= 1
    return r

# trace to F_2 for F_{2^e}: Tr(x) = sum_{i=0}^{e-1} x^{2^i}
def gf2_trace(x, mod, deg):
    s = 0
    t = x
    for _ in range(deg):
        s ^= t
        t = gf2_mul(t, t, mod, deg)
    return s & 1   # element of F_2 (the trace lands in {0,1} as the constant poly)

# primitive polys for F_{2^e}
PRIM = {3:0b1011, 4:0b10011, 5:0b100101, 6:0b1000011}

def gold_spectrum(e, k):
    mod = PRIM[e]; deg = e
    d = (1 << k) + 1   # Gold exponent 2^k + 1
    N = (1 << e)
    vals = []
    for tau in range(1, N):     # tau in F_{2^e}^*
        c = 0
        for x in range(N):      # x in F_{2^e}
            xd = gf2_pow(x, d, mod, deg)
            taux = gf2_mul(tau, x, mod, deg)
            arg = xd ^ taux
            c += (-1) ** gf2_trace(arg, mod, deg)
        vals.append(c)
    return vals, N

def main():
    print("="*78)
    print("(I) HGG Gold-decimation cross-correlation: the FEW-VALUED spectrum and its PEAK scale")
    print("="*78)
    for e in [4,5,6]:
        for k in [1,2]:
            if math.gcd(k, e) != 1:   # Gold 3-valued needs gcd(k,e)=1
                continue
            vals, N = gold_spectrum(e, k)
            cnt = Counter(vals)
            peak = max(abs(v) for v in vals)
            sqrtN = math.sqrt(N)
            print(f"  F_2^{e} (N={N}), Gold d=2^{k}+1: spectrum = {dict(sorted(cnt.items()))}")
            print(f"     #distinct = {len(cnt)} (HGG: 3-valued)   PEAK |C| = {peak}"
                  f"   sqrt(N)={sqrtN:.2f}  peak/sqrt(N) = {peak/sqrtN:.3f}")
    print("  => HGG few-valued PEAK is Theta(sqrt(field)) and >= sqrt(N): a sqrt-of-FIELD scale,")
    print("     never below. (Welch/Sidelnikov is tight here -- the sqrt floor IS the answer.)")

    # ---------- (II) the prize object vs HGG/Weil 'sqrt(field)' scale ----------
    print("\n" + "="*78)
    print("(II) Prize object eta_b over thin mu_n < F_p^*: which 'field size' does HGG sqrt deliver?")
    print("     If HGG-coerced, the Weil/full-field scale is sqrt(p) -- VACUOUS on the n-domain.")
    print("="*78)
    def is_prime(x):
        if x<2: return False
        if x%2==0: return x==2
        i=3
        while i*i<=x:
            if x%i==0: return False
            i+=2
        return True
    def primroot(p):
        phi=p-1; m=phi; facs=set(); d=2
        while d*d<=m:
            if m%d==0:
                facs.add(d)
                while m%d==0: m//=d
            d+=1
        if m>1: facs.add(m)
        for gg in range(2,p):
            if all(pow(gg,phi//f,p)!=1 for f in facs): return gg
    def find_prime(n,beta=3.2):
        t=int(n**beta); m=max(2,t//n)
        while True:
            p=1+n*m
            if p>t and is_prime(p): return p,m
            m+=1
    for mu_exp in [3,4,5]:
        n=2**mu_exp; p,m=find_prime(n); g=primroot(p)
        mm=(p-1)//n; gen=pow(g,mm,p)
        mu=[]; x=1
        for _ in range(n):
            mu.append(x); x=(x*gen)%p
        w=exp(2j*pi/p)
        M=max(abs(sum(w**((b*xx)%p) for xx in mu)) for b in range(1,p))
        sqrtp=math.sqrt(p); prize=math.sqrt(2*n*math.log(m))
        print(f"  n={n} p={p} m={m}:  M={M:.3f}   sqrt(p) [HGG/Weil full-field scale] = {sqrtp:.3f}"
              f"   prize sqrt(2 n log m) = {prize:.3f}")
        print(f"       M/sqrt(p) = {M/sqrtp:.4f} (Weil VACUOUS: gives <= sqrt(p) >> n>=M)   "
              f"M/prize = {M/prize:.3f}")
    print("\n" + "="*78)
    print("VERDICT: HGG few-valued spectra deliver a sqrt(FIELD) peak; coercing eta_b into HGG")
    print("form makes 'field' = F_p, so HGG => |eta_b| <= O(sqrt p), the already-DEAD plain-Weil")
    print("bound (vacuous: sqrt(p) >> n on the n-domain). HGG offers NO sub-Welch UPPER bound for")
    print("the thin-subgroup peak. Reduces to BGK/Welch-floor; no push past 0.011 toward 1/2.")
    print("="*78)

if __name__ == "__main__":
    main()

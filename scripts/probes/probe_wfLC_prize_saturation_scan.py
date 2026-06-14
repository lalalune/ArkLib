#!/usr/bin/env python3
"""
LANE LC (#407) — DIRECT F_p scan: does ANY prize-scale prime saturate the worst direction
at the binding band (= char-p excess, breaking faithfulness)?

Saturation of monomial dir(a,b) on a w-subset T (= incidence jumps to q, char-p EXCESS over the
char-0 value)  <=>  the complete-homogeneous readout  h_{b-k}(omega^T) = 0  in F_p, where omega is
a primitive n-th root mod p.  (In-tree mechanism: probe_mergeonly_saturation_refute.py, Schur-bridge
dichotomy 02:28.)  This is pure modular arithmetic => FAST, so we can scan MANY prize-scale primes.

We scan ALL primes p = n*m+1 (odd index m) with n^4 <= p <= cap, and for each, test EVERY w-subset
T at the binding band(s) for h_{b-k}(omega^T) ≡ 0.  A single hit at a band where char-0 does NOT
vanish  =>  char-p EXCESS at prize scale  =>  REFUTES worst-direction faithfulness (delta* < edge).
Zero hits across the full prize-scale scan + (separately verified) char-0 nonvanishing  =>  strong
FAITHFUL evidence (per-fixed-n) at the worst direction.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import isprime
from itertools import combinations_with_replacement

def prim_root(p):
    from prize_workspace import prime_factors
    fz = prime_factors(p-1)
    for g in range(2, p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fz): return g
    raise RuntimeError

def omega_n(p, n):
    g = prim_root(p); return pow(g,(p-1)//n,p)

def h_mod(deg, idxs, w_vals, p):
    """h_deg evaluated at {w_vals[i] : i in idxs} mod p."""
    xs = [w_vals[i] for i in idxs]
    s = 0
    for combo in combinations_with_replacement(range(len(xs)), deg):
        t = 1
        for c in combo: t = t*xs[c] % p
        s = (s+t) % p
    return s

def _h_complex(deg, T, n):
    import cmath, math
    z = [cmath.exp(2j*math.pi*t/n) for t in T]
    s = 0+0j
    for combo in combinations_with_replacement(range(len(z)), deg):
        t = 1+0j
        for ci in combo: t *= z[ci]
        s += t
    return s

def scan(n, k, a, b, ws, p_lo, p_hi):
    """Scan prize primes in [p_lo,p_hi]; return (#primes, list of GENUINE-EXCESS (p,w,T) hits).
       GENUINE EXCESS = h≡0 mod p AND h != 0 over ℂ on the SAME T (else it's char-0 vanishing reduced)."""
    deg = b - k
    # precompute char-0-zero subsets per w (EXCLUDE them — they are not excess)
    c0zero = {w: set(T for T in itertools.combinations(range(n), w) if abs(_h_complex(deg,T,n))<1e-6) for w in ws}
    hits = []; nP = 0
    p = p_lo - (p_lo % n) + 1
    if p < p_lo: p += n
    while p <= p_hi:
        m = (p-1)//n
        if m % 2 == 1 and isprime(p):
            nP += 1
            wv = [pow(omega_n(p,n), t, p) for t in range(n)]
            found = False
            for w in ws:
                for T in itertools.combinations(range(n), w):
                    if T in c0zero[w]:        # char-0 already zero here -> NOT excess
                        continue
                    if h_mod(deg, T, wv, p) == 0:
                        hits.append((p, w, T)); found = True; break
                if found: break
        p += n
    return nP, hits

def char0_zero_count(n, deg, ws):
    """exact count of w-subsets T with h_deg(zeta^T)=0 over ℂ (per band) — must be 0 for EXCESS to mean excess."""
    import cmath, math
    out = {}
    for w in ws:
        c = 0
        for T in itertools.combinations(range(n), w):
            z = [cmath.exp(2j*math.pi*t/n) for t in T]
            s = 0+0j
            for combo in combinations_with_replacement(range(len(z)), deg):
                t = 1+0j
                for ci in combo: t *= z[ci]
                s += t
            if abs(s) < 1e-6: c += 1
        out[w] = c
    return out

if __name__ == '__main__':
    print("="*82)
    print("LANE LC DIRECT F_p prize-scale saturation scan (worst-dir h_{b-k} ≡ 0 mod p)")
    print("="*82)
    # n=16, worst dir(4,10): deg = b-k = 6.  Binding bands w in {5,6,7} (around delta*=9/16..).
    # Prize scale: n^4 = 65536 .. cap.
    for (n,k,a,b,ws,cap,lab) in [
        (16,4,4,10,[5,6,7], 16**4 + 200000, "n=16 worst dir(4,10) deg6"),
        (16,4,7,7,[5,6],    16**4 + 200000, "n=16 h_3 readout deg3 (b=7,k=4)"),
    ]:
        c0 = char0_zero_count(n, b-k, ws)
        nP, hits = scan(n,k,a,b,ws, 16**4, cap)
        print(f"\n{lab}: scanned {nP} prize primes in [{n**4}, {cap}] (odd index)")
        print(f"  char-0 vanishing w-subset counts (must be 0 for EXCESS): {c0}")
        if hits:
            print(f"  *** SATURATION HITS (char-p EXCESS at prize scale): {len(hits)} ***")
            for (p,w,T) in hits[:5]:
                print(f"      p={p}=n^{__import__('math').log(p)/__import__('math').log(n):.3f} w={w} T={T}")
            print("  => REFUTES worst-direction faithfulness: delta* < Kambire edge")
        else:
            print("  NO saturation across all prize primes scanned => FAITHFUL (per-fixed-n) at worst dir")

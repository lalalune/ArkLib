#!/usr/bin/env python3
"""
wf-LE (#407): low-exponent (bounded #S) height-gate depth at the PRIZE scale.

The full-subset gate is intrinsically capped at n=64 (worst-case norm = (n/2-1)^{n/4},
confirmed exact at n=8,16). BUT the proximity object only needs the BINDING-SCALE
relations: short +/- relations of length w ~ 2*ceil(log2 m) = the deep-moment depth.
The min-weight floor target is W(n,p) >= 2 ceil(log m).

For bounded #S = t, the structure-aware norm bounds give per-conjugate modulus <= t
(house) or, by L2/Mahler (AM-GM on squares fed by Parseval mass <= n*t):
    |N|^2 <= (mean of |sigma Sigma_S|^2)^{phi}  <= ( n*t / phi )^{phi} = (2t)^{n/2}
    => |N| <= (2t)^{n/4}.
Gate closes for given (n, t) at prize p ~ n*2^128 iff  (2t)^{n/4} <= n*2^128, i.e.
    (n/4) log2(2t) <= 128 + log2 n.

This probe:
 (1) tabulates the MAX t closed by L2 vs house at prize scale, across n = 2^a up to 2^30;
 (2) compares against the binding depth target  w* = 2*ceil(log2 m), m = (q-1)/n = 2^128;
 (3) the SHARPER per-set bound: for a *specific* low-weight S the realized norm is far
     below (2t)^{n/4}; measure realized norm for the worst t-subset at small n to get the
     true t-exponent c(t) with realized|N| ~ 2^{c(t)*?}.
"""
import math, itertools
import sympy as sp

x = sp.symbols('x')
def Phi(n): return sp.Poly(x**(n//2)+1, x)
def norm_sub(S,n): return abs(int(sp.resultant(sp.Poly(sum(x**i for i in S),x), Phi(n).as_expr())))

def max_t_closed(n, log2p, bound):
    # bound: 'house' -> (t)^{n/2} ; 'l2' -> (2t)^{n/4}
    best = 0
    for t in range(1, n+1):
        if bound=='house':
            lhs = (n/2)*math.log2(t) if t>0 else 0
        else:
            lhs = (n/4)*math.log2(2*t)
        if lhs <= log2p:
            best = t
    return best

print("== (1)/(2): max #S closed at prize scale (log2 p = a + 128) vs binding depth 2*ceil(log2 m), m=2^128 ==")
print(f"{'a':>3} {'n':>12} {'log2p':>6} {'house t<=':>10} {'l2 t<=':>8} {'bindingDepth':>13} {'l2>=depth?':>10}")
for a in [7,8,10,16,20,30,32,43]:
    n = 2**a
    log2p = a + 128
    ht = max_t_closed(n, log2p, 'house')
    lt = max_t_closed(n, log2p, 'l2')
    # m = (q-1)/n ~ 2^128 ; depth = 2*ceil(log2 m) = 2*128 = 256 (FIXED, since m=2^128 fixed)
    m_bits = 128
    depth = 2*math.ceil(m_bits)  # 2*ceil(log2 m)
    ok = "YES" if lt >= depth else "no"
    print(f"{a:>3} {n:>12} {log2p:>6} {ht:>10} {lt:>8} {depth:>13} {ok:>10}")

print()
print("== (3): realized worst t-subset norm exponent c(t) (n=16,32 exact-ish) vs bound (2t)^{n/4} ==")
print("   realized|N| for worst t-subset, t small; compare to L2 prediction.")
for n in [16]:
    print(f"  n={n}:")
    for t in range(2, 9):
        best=0; bS=None
        for S in itertools.combinations(range(n), t):
            v = norm_sub(S,n)
            if v>best: best=v; bS=S
        rb = math.log2(best) if best>0 else 0
        l2 = (n/4)*math.log2(2*t)
        house = (n/2)*math.log2(t) if t>0 else 0
        print(f"    t={t}: realized {rb:7.3f} bits | L2 {l2:7.3f} | house {house:7.3f} | worstS {bS}")

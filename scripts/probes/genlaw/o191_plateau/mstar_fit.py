#!/usr/bin/env python3
"""
mstar_fit.py  (#444 -- the DECISIVE object m* on the powers-of-2 tower: ADDITIVE vs LINEAR fit)

m*(n) = min{ m = s-k : D*_n(m) <= budget=n }, k=n/4 (rate 1/4). The object whose growth IS the
dichotomy: m* = O(log n) => prize HOLDS (additive |P|); m* = Theta(n) => prize FAILS (multiplicative).

PROVENANCE:
  [GPU]  m*(8,12,16,20,24,28,32) = 3,4,3,4,5,6,5  -- authoritative exhaustive worst-direction GPU
         cascade rho4.out (pg.cu maximizes over ALL far directions; exact, q~n^4).
  [E5]   the dyadic cascade recursion D*_{2n}(m) = D*_n(m-1) EXCEPT plateau-doubling at the
         imprimitive worst direction, where w(2n)=v2(gcd(b-a,2n)) extra rungs insert. VERIFIED on
         the exact cascades: D*_32(3)=D*_16(2)=89 (off-plateau transfer holds); the binding value 9
         shifts from m=3 (n=16) to m=5 (n=32), increment = 2 = w(32). => m*(2n)=m*(n)+w(2n) at the
         one clean tower step 16->32.
  [O183] crossing #bad = 1 + (#orbits)*S <= n, S=n/gcd=8 constant; budget crossing O <= (n-1)/8.
  [FIT]  growth-law fit. NOT a proof.

HONEST CAVEAT: the recursion increment "= w(2n)" is EQUALITY-verified at ONLY ONE clean step
(16->32); n=8 is the primitive boundary base where it does NOT hold (predicts 4, real 3). So
m*(64), m*(128) below are RECURSION-EXTRAPOLATED [E5/FIT], not brute-confirmed (C(64,24) intractable).
The rho4 cascade at n>=64 cannot be brute-forced; this is the named open computational gap and the
extrapolation is reported AS an extrapolation, tagged, never as an exact datum.
"""
import math

def v2(x):
    v=0
    while x>0 and x%2==0: v+=1; x//=2
    return v
def worst(n): return (5*n//8, n//4)
def w(n):
    e,f=worst(n); return v2(math.gcd(n,abs(e-f)))

# EXACT [GPU]
GPU = {8:3, 12:4, 16:3, 20:4, 24:5, 28:6, 32:5}

print("="*90)
print("DECISIVE OBJECT m*(n): exact [GPU] data + the two in-tree readings it must adjudicate")
print("="*90)
print(f"{'n':>4} {'k=n/4':>6} {'m*[GPU]':>8} {'n/4-1(line)':>12} {'dip=line-m*':>12} {'pow2?':>6}")
for n in sorted(GPU):
    line = n//4 - 1
    dip = line - GPU[n]
    p2 = 'POW2' if (n&(n-1))==0 else ''
    print(f"{n:>4} {n//4:>6} {GPU[n]:>8} {line:>12} {dip:>12} {p2:>6}")

print()
print("READING 1 (DecouplingCrossingDepthGrowsInN): pow2 subseq m*(8,16,32)=3,3,5 is SUB-LINEAR")
print("         -> favorable, prize-LEANS-HOLD.  m*(32)=5 CONTRADICTS line m*=n/4-1=7.")
print("READING 2 (CrossingDepthLinearTracking):     mid-range n=16,20,24,28 -> m*=3,4,5,6 = n/4-1")
print("         EXACTLY (LINEAR); pow2 is a bounded 2-adic DIP -> prize-FAILS horn.")
print("THE GAP: which way does the POW2 dip go at n=64,128? dip(16)=0, dip(32)=2 (GROWING so far).")
print()

# ---- m* on the pow2 tower via E5 recursion (increment = w(2n)), tagged [E5/FIT] ----
print("="*90)
print("m* on the POWERS-OF-2 TOWER via the E5+plateau recursion m*(2n)=m*(n)+w(2n)  [E5/FIT]")
print("="*90)
mt = {16:3, 32:5}   # EXACT [GPU] anchors (n=8 excluded: primitive boundary, recursion fails there)
print(f"  anchor m*(16)=3 [GPU], m*(32)=5 [GPU] (recursion increment w(32)=2 VERIFIED exact)")
for n in (64,128):
    inc = w(n)
    mt[n] = mt[n//2] + inc
    print(f"  m*({n}) = m*({n//2}) + w({n}) = {mt[n//2]} + {inc} = {mt[n]}   [E5/FIT extrapolation]")

print()
seq_n   = [16,32,64,128]
seq_m   = [mt[n] for n in seq_n]
seq_lin = [n//4-1 for n in seq_n]
seq_dip = [seq_lin[i]-seq_m[i] for i in range(4)]
print(f"  m* (pow2, E5):   n=16,32,64,128 -> {seq_m}")
print(f"  LINEAR n/4-1:    n=16,32,64,128 -> {seq_lin}")
print(f"  DIP (line - m*): n=16,32,64,128 -> {seq_dip}   (GROWS ~ quadratically -> m* SUB-LINEAR)")

print()
print("="*90)
print("THE FIT: additive O(log n) vs multiplicative/linear  (mu = log2 n)")
print("="*90)
import math as M
print(f"{'n':>5} {'mu=log2n':>9} {'m*(E5)':>8} {'m*/mu':>8} {'m*/n':>10} {'2*m*(n/2)':>10} {'n/4-1':>7}")
for i,n in enumerate(seq_n):
    mu = int(M.log2(n)); m=seq_m[i]
    mult = 2*mt[n//2] if n//2 in mt else None
    print(f"{n:>5} {mu:>9} {m:>8} {m/mu:>8.3f} {m/n:>10.4f} {str(mult):>10} {n//4-1:>7}")

print()
print("INTERPRETATION:")
print(f"  * MULTIPLICATIVE (w(2n)=2w(n)): would give m*(32)=2*m*(16)=6. REAL m*(32)=5. REFUTED at n=32.")
print(f"  * LINEAR n/4-1: m*(32)=7. REAL=5. REFUTED at n=32 (the 2-adic dip).")
print(f"  * m*/n -> {seq_m[-1]/seq_n[-1]:.4f} and SHRINKING ({[round(seq_m[i]/seq_n[i],4) for i in range(4)]})")
print(f"    => m* is SUB-LINEAR on the tower (m*/n -> 0): the FAVORABLE lean EXTENDS past n=32.")
print(f"  * BUT m* is NOT O(log n) either: m*/mu = {[round(seq_m[i]/int(M.log2(seq_n[i])),3) for i in range(4)]} ")
print(f"    is GROWING -> m* ~ Theta(log^2 n) (increment w=mu-2 grows), the CoreA4 polylog envelope.")
print(f"    Differences m*(2n)-m*(n) = {[seq_m[i+1]-seq_m[i] for i in range(3)]} = w = {[w(n) for n in (32,64,128)]} (arithmetic, not const).")
print()
print("VERDICT on the decisive object (this PROXY face, recursion-extrapolated beyond n=32):")
print("  m* is SUB-LINEAR (m*/n->0) -- AGAINST the prize-FAILS multiplicative/linear horn --")
print("  but is super-O(log n) (~log^2 n): NOT the clean additive O(log n) prize either.")
print("  The dip GROWS (0,2,7,19), confirming sub-linear; n<=128 still cannot separate log^2 from")
print("  slow-poly. LEANS-ADDITIVE in the weak sense (sub-linear, prize-not-refuted), NOT a proof.")

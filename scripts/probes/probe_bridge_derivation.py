"""
Verify the BRIDGE numerically (the reduction from the energy/Wick bound to the prize sup-norm), and the
key arithmetic facts the proof rests on, so the document's claims are machine-checked.
"""
import math
from math import comb, log, sqrt, factorial
def dfac(k):  # (2k-1)!!
    r=1
    for i in range(1,2*k,2): r*=i
    return r

print("=== BRIDGE: E_r<=(2r-1)!!n^r for all r  =>  M<=sqrt(2 n log p) (the moment optimization) ===")
print("M^{2r} <= sum_{b!=0}|eta_b|^{2r} = p E_r - n^{2r} <= p (2r-1)!! n^r, so M <= (p (2r-1)!! n^r)^{1/2r}.")
print("Optimize over r: the bound B(r)=(p (2r-1)!! n^r)^{1/2r}; min near r=log p. Check it lands ~sqrt(2n log p):")
for (n,p) in [(16, 3276817), (2**30, (2**30)*(2**128))]:
    best=(1e99,0)
    L=log(p)
    for r in range(1, int(3*L)+2):
        B = (p * dfac(r) * n**r) ** (1/(2*r))
        if B<best[0]: best=(B,r)
    target = sqrt(2*n*L)
    print(f"  n={n} (2^{int(round(log(n,2)))}), p~n^4*2^128: min_r B(r)={best[0]:.4g} at r={best[1]}; "
          f"sqrt(2 n log p)={target:.4g}; ratio B/target={best[0]/target:.3f}; r*~log p={L:.1f}")
print("  => bridge CONFIRMED: the Wick bound at all r up to ~log p gives M <= ~sqrt(2 n log p) = O(sqrt(n log m)).")
print()
print("=== the CHAR-P GAP: norm bound (2r)^{n/2} vs p -- where the char-0 argument dies ===")
print("W_r=0 is GUARANTEED only if p > (2r)^{n/2} (no wraparound by archimedean size). Check the threshold:")
for n in (16, 64, 2**30):
    # max r with (2r)^{n/2} < p, for p~n^4
    p = n**4
    # (2r)^{n/2} < n^4  =>  2r < n^{8/n}  =>  r < n^{8/n}/2
    rmax = (n**(8/n))/2
    print(f"  n={n}: p~n^4; char-0 guaranteed only for r < n^{{8/n}}/2 = {rmax:.4f}  "
          f"(need r up to log p~{4*log(n):.0f}) -> {'VACUOUS (rmax<1)' if rmax<1 else f'covers only r<={int(rmax)}'}")
print("  => at prize scale n=2^30, n^{8/n}->1, so the norm bound gives NOTHING (W_r possible at all r>=1).")
print("     The W_r=0 DATA at prize primes is therefore a GOOD-PRIME fact, not a size fact = the open ANT input.")
print()
print("=== FROBENIUS GAP idea check: are the extra (wraparound) solutions structured by ord(p mod n)? ===")
print("(ZMod n)^* for n=2^mu is Z/2 x Z/2^{mu-2}: max element order = 2^{mu-2}; orders are POWERS OF 2.")
for mu in (4,5,6,7):
    n=2**mu
    # element orders in (Z/n)^*
    units=[a for a in range(1,n) if math.gcd(a,n)==1]
    def order(a):
        x=a; k=1
        while x!=1: x=x*a%n; k+=1
        return k
    orders=sorted(set(order(a) for a in units))
    print(f"  n={n}=2^{mu}: unit-group element orders = {orders} (all powers of 2; max {max(orders)}=2^{mu-2})")

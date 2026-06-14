#!/usr/bin/env python3
"""
FINAL adversarial test: is the remaining lemma a KNOWN WALL (Paley/BGK) or strictly weaker?

The skeleton claims:  [A_r <= Wick for all r <= ~log p]  <=>  M <= C sqrt(n log p)  (Paley/BGK).

(=>) GRANTED and verified: optimize at r~log p.  Already confirmed C~1.

(<=) The reverse: does the existence of the *single-r* bound A_r0 <= Wick at ONE well-chosen
     r0 ~ log p already give M <= C sqrt(n log p)?   YES trivially:
        M^{2 r0} <= sum_{b!=0}|eta_b|^{2 r0} = p A_{r0} <= p Wick(n,r0),
        so M <= (p (2r0-1)!! n^{r0})^{1/(2 r0)} ~ sqrt(2 n ln p) at r0~ln p.
     So we DON'T even need all r -- ONE r0 ~ log p suffices.  CONFIRM that the bound at the
     single optimal r0 is what's needed, and that A_{r0}<=Wick at r0~log p is the ENTIRE content.

CONCLUSION TEST: The remaining lemma 'A_{r0} <= Wick at r0 ~ log p (equiv Anom_{r0} <= n^{2r0}/p)'
is therefore EXACTLY as strong as the prize sup-norm bound M <= C sqrt(n log p), which is the
Paley-graph / square-root-cancellation conjecture for a size-n subgroup.  Best PROVEN: n^{0.989}
(di Benedetto, n>p^{1/4}) and n^{1-o(1)} (BGK). So the remaining lemma at the prize r0 is NOT
provable by any current technique.

Here we just numerically pin the equivalence at the single optimal r0 and show that the gap
between 'what we can prove (n^{0.989} or worse)' and 'what we need (A_{r0}<=Wick)' is real:
   the n^{0.989} bound gives A_{r0} <= p * (n^{0.989})^{2 r0} / ... -- compute and show it does
   NOT give A_{r0} <= Wick (i.e. the SOTA is too weak even granting it, at the prize r0).
"""
import math
def doublefact(r):
    d=1.0
    for j in range(1,2*r,2): d*=j
    return d
def wick(n,r): return doublefact(r)*n**r

print("="*92)
print("Single-r0 reduction:  M <= (p*Wick(n,r0))^{1/2r0}.  Pick r0=round(ln p).  C := M_bound/sqrt(n ln p)")
print("="*92)
for (logn,beta) in [(10,4),(20,4),(30,4),(30,5)]:
    n=2**logn; lnp=beta*logn*math.log(2)
    r0=max(1,round(lnp))
    logMb=(math.log(beta)+logn*math.log(2)+math.log(doublefact(r0))+r0*logn*math.log(2))/(2*r0)
    # p = n^beta = 2^(logn*beta); log p = beta*logn*log2
    logMb=(beta*logn*math.log(2)+math.log(doublefact(r0))+r0*logn*math.log(2))/(2*r0)
    Mb=math.exp(logMb)
    print(f"n=2^{logn} beta={beta}: r0={r0}  M_bound={Mb:.1f}  sqrt(n ln p)={math.sqrt(n*lnp):.1f}  C={Mb/math.sqrt(n*lnp):.4f}")
print()
print("="*92)
print("Does SOTA (M <= n^{0.989}) even SUFFICE to give A_{r0}<=Wick at the prize r0?")
print("  If M<=n^c then A_r <= (p-1)/p * (worst per-b) ... no; better: A_r <= sum |eta|^2r weighted.")
print("  Use the moment lift the OTHER way: M<=n^c does NOT bound A_r below; it gives an UPPER")
print("  bound on M but the prize NEEDS c=1/2+o(1). Show n^{0.989} >> sqrt(n log p):")
print("="*92)
for (logn,beta) in [(10,4),(20,4),(30,4)]:
    n=2**logn; lnp=beta*logn*math.log(2)
    sota=n**(1-31/2880)          # di Benedetto exponent
    bgk_like=n/ (logn**2)         # illustrative n^{1-o(1)} stand-in (not literal)
    target=math.sqrt(2*n*lnp)
    print(f"n=2^{logn}: SOTA n^0.989 = {sota:.3e}   prize target sqrt(2 n ln p)={target:.3e}   "
          f"SOTA/target = {sota/target:.2e}  (need this -> O(1); it's ~sqrt(n)/polylog)")
print()
print("VERDICT: SOTA exceeds the prize target by a factor ~ n^{1/2-31/2880}/polylog ~ n^{0.49}.")
print("So no current bound reaches A_{r0}<=Wick at r0~log p in the prize regime. WALL confirmed.")
print("Note also di Benedetto REQUIRES n>p^{1/4} i.e. p<n^4; prize p=n^4 is the boundary, p>n^4 unproven.")

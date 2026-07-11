#!/usr/bin/env python3
"""
probe_dsj_n16_witness_check.py (#444)
Directly re-verify the in-tree FloorAsymptotic decide-witnesses and ask whether
they REFUTE the prompt's s*(n)=n/2+1-2(log2 n -3) formula.

In-tree (axiom-clean `decide`, ArkLib FloorAsymptoticRadius.lean):
  mu8  in ZMod 17, fwit8(x)=2+16x+15x^4+x^5  has 5 zeros on mu_8  (deg<=5, 4 monomials nonzero const? count terms)
  mu16 in ZMod 17, fwit16(x)=9+16x^2+8x^8+x^10 has 10 zeros on mu_16

Sparse-zero radius interpretation: a poly with SUPPORT size t (# monomials) can
vanish at up to ??? points of mu_n. fwit8 support = {0,1,4,5} -> 4 monomials, 5 zeros.
fwit16 support = {0,2,8,10} -> 4 monomials, 10 zeros.

The PROMPT object s* is an OVER-DETERMINED far-line incidence: a degree-<k=n/4 codeword
agreeing with a fixed received word in s positions, s as large as possible while the
agreement still 'over-determines' (forces) the codeword. For RS that's just: two distinct
degree-<k polys agree in <= k-1 points (over-det boundary at s=k). The 'far line' adds a
direction; worst-dir incidence is a Johnson-type bound. Let me just check what the
fwit witnesses MEAN for s*.
"""
p=17
def order(x,p):
    o=1; y=x%p
    while y!=1:
        y=y*x%p; o+=1
    return o

# mu_8 = 8th roots of unity in F_17
mu8=[pow(x,1,p) for x in range(1,p) if pow(x,8,p)==1]
mu16=list(range(1,p))  # all 16 nonzero = mu_16 since 17 prime, group order 16

def f8(x): return (2+16*x+15*pow(x,4,p)+pow(x,5,p))%p
def f16(x): return (9+16*pow(x,2,p)+8*pow(x,8,p)+pow(x,10,p))%p

z8=[x for x in mu8 if f8(x)==0]
z16=[x for x in mu16 if f16(x)==0]
print("mu8 =", sorted(mu8), "card", len(mu8))
print("fwit8 zeros:", sorted(z8), "count", len(z8))
print("fwit16 zeros count:", len(z16))
print()
# fwit8: support degrees with nonzero coeff
sup8=[d for d,c in [(0,2),(1,16),(4,15),(5,1)] if c%p]
sup16=[d for d,c in [(0,9),(2,16),(8,8),(10,1)] if c%p]
print("fwit8 support (monomial degrees):", sup8, "size", len(sup8), "-> zeros", len(z8))
print("fwit16 support:", sup16, "size", len(sup16), "-> zeros", len(z16))
print()
# KEY: For RS code of degree < k, a NONZERO poly of degree < D vanishes at <= D-1 points.
# fwit8 has degree 5, vanishes at 5 points of mu_8. deg=5 => <=5 zeros total, achieves 5.
# fwit16 has degree 10, vanishes at 10 points. deg=10 => <=10 zeros, achieves 10.
# This is just 'degree-d poly has up to d roots' SATURATED on the subgroup.
# s* in the prompt = n/2+1-2(log-3). For the SPARSE-ZERO radius to equal s*,
#  n=8: deg-5 poly, 5 zeros => radius indicator 5 = prompt 5. OK.
#  n=16: a deg-? poly. prompt says 7. But fwit16 (deg 10) already gives 10 zeros!
print("REFUTATION TEST: prompt s*(16)=7 but explicit deg-10 poly has 10 zeros on mu_16.")
print(" => If s* is the sparse-zero / max-agreement radius, 10 > 7 REFUTES prompt formula.")
print(" => prompt s* must therefore be a DIFFERENT (over-determined incidence) object,")
print("    OR the prompt formula is wrong / fit to too few points (n=8 only true match).")

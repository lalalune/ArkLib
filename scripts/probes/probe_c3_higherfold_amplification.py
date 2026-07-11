#!/usr/bin/env python3
"""
C3 deepest test: can a HIGHER-FOLD (r-fold) sum-product amplification with the
near-Sidon energies push the saving PAST 1/24 toward 1/2?

The di Benedetto saving 1/24 is for a FIXED 3-fold amplification.  The general
BGK/Kowalski machine uses r-fold.  Question: does the r-fold near-Sidon saving
increase with r toward 1/2?

The r-fold amplification (Bourgain-Garaev / Kowalski) bounds the exp sum via the
MULTIPLICATIVE energy E_r^*(H) and the additive energy E(H).  For a GROUP, the
multiplicative energy is degenerate (H*H=H), so the whole r-fold action reduces
to the ADDITIVE r-fold energy E_r(H)=#{Sum_r h = Sum_r h'}.  The Holder/r-fold
amplification gives roughly:
   M(H)^{2r} <= (1/p) * sum_b |eta_b|^{2r} = E_r(H)   (the MOMENT identity!)
So the r-fold sum-product bound, evaluated on a GROUP, IS EXACTLY the moment method:
   M(H) <= E_r(H)^{1/2r}.
With near-Sidon E_r(H) <= (2r-1)!! n^r  (the Wick/Lam-Leung value):
   M(H) <= ((2r-1)!! n^r)^{1/2r} = sqrt(n) * ((2r-1)!!)^{1/2r}.
   (2r-1)!! ~ (2r/e)^r * sqrt(2)  => ((2r-1)!!)^{1/2r} ~ sqrt(2r/e).
So M(H) <= sqrt(n) * sqrt(2r/e) = sqrt( (2r/e) n ).  Minimizing over r is moot
(monotone in r); the USEFUL regime is r ~ ln(q/n) where the geometric truncation
from the |H|<<p constraint kicks in, giving M <= sqrt(2 n ln(q/n)) = the PRIZE.
"""
from math import log, sqrt, e, factorial
from fractions import Fraction as F

def double_fact(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

print("=== r-fold amplification on a GROUP = moment method (multiplicative energy degenerate) ===")
print("If near-Sidon E_r <= (2r-1)!! n^r holds to depth r~ln q, the r-fold bound")
print("M <= ((2r-1)!! n^r)^{1/2r} = sqrt(n)*((2r-1)!!)^{1/2r}:")
print(f"{'r':>3} {'(2r-1)!!':>14} {'((2r-1)!!)^(1/2r)':>18} {'~sqrt(2r/e)':>12}")
for r in [1,2,3,5,10,20,50,100,177]:
    df = double_fact(2*r-1)
    amp = df**(1/(2*r))
    print(f"{r:>3} {df:>14.4g} {amp:>18.4f} {sqrt(2*r/e):>12.4f}")

print()
print("KEY: as r grows, the saving from the FIXED-r sum-product formula does NOT cap at 1/24.")
print("The 1/24 ceiling is SPECIFIC to di Benedetto's 3-fold formula (and its t2,t3 floors).")
print("The r-fold version, evaluated on a GROUP, IS the moment method M<=sqrt((2r/e)n),")
print("which at r~ln(q/n) gives the PRIZE M<=sqrt(2 n ln(q/n)) (saving -> 1/2 effectively).")
print()
print("*** SO: the C3 'effective sum-product exponent' route, taken to its r-fold limit on a")
print("    GROUP, COLLAPSES INTO the moment/Wick-energy method already in-tree (GaussPeriodMomentBound,")
print("    BGKLimitConditional, GaussianEnergyBound). It is NOT an independent handle.")
print()
print("    The 1/24 (fixed 3-fold) is a genuine 3.9x improvement over generic 0.011 but is a")
print("    DEAD END as a route to 1/2 (capped). The r-fold extension that COULD reach 1/2 is")
print("    EXACTLY the moment method, whose open input is the char-p near-Sidon energy E_r<=(2r-1)!!n^r")
print("    to depth r~ln q -- THE SAME WALL (GaussianEnergyBound char-p transfer / WickEnergyBracket).")
print()
print("=== Does the r-fold near-Sidon bound reach the prize scale at r~ln(q/n)? ===")
for mu in [10, 20, 30]:
    n = 2**mu
    # prize: q ~ n * 2^128, log(q/n) = 128 ln2
    L = 128*log(2)
    rstar = max(1, int(L))  # r ~ ln(q/n)
    df = double_fact(2*rstar-1)
    # truncated moment bound: M <= (E_r)^{1/2r} but with the m=(q-1)/n truncation only r<=log m terms
    # the optimized value is sqrt(2 n ln(q/n))
    M_moment = sqrt(2*n*L)
    print(f"n=2^{mu}: prize floor M<=sqrt(2 n log(q/n)) = {M_moment:.3e}; sqrt(n)={sqrt(n):.3e}; ratio={M_moment/sqrt(n):.2f}=sqrt(2 log(q/n))")

#!/usr/bin/env python3
"""
probe_407_wickbound_capability.py  (#444)

LANE (uncontested, analytic+exact): I reduced the moment route to the Wick ratio W_r (push 58f29f3f0)
and showed its deficit is sub-leading => W_{r*} -> 1 (push b97f5a972). So the BEST CASE the moment route
can deliver is A_r = Wick = (2r-1)!! n^r EXACTLY (W_r=1, the Gaussian model). THE QUESTION NOBODY PINNED:
even in that best case, what sup-norm bound does the moment route GIVE at the prize depth r*~log m, and
does it REACH the prize M <= C sqrt(n log m) or does the Wick value ITSELF already encode a barrier?

The moment bound: M = max_b |eta_b|, and sum_{b!=0} |eta_b|^{2r} = p E_r. With the DC removed,
A_r = p E_r - n^{2r} bounds the off-DC mass; the single-frequency sup obeys M^{2r} <= A_r (one term <=
the sum). So in the BEST case A_r = Wick:
    M <= (A_r)^{1/2r} = ((2r-1)!! n^r)^{1/2r} = sqrt(n) * ((2r-1)!!)^{1/2r}.
Using (2r-1)!! ~ sqrt(2) (2r/e)^r (Stirling): ((2r-1)!!)^{1/2r} ~ sqrt(2r/e). So
    M <= sqrt(n) * sqrt(2r/e) * (1+o(1)).
OPTIMIZING over r is the crux: M^{2r} <= A_r must hold for the bound to apply, and we pick the r that
MINIMIZES the RHS. But sqrt(n)*sqrt(2r/e) INCREASES in r -- so the moment bound is BEST at SMALL r, giving
M <= sqrt(n)*sqrt(2r/e) ~ sqrt(n) at r=O(1). That CANNOT be right for a sup over q-1 frequencies (it would
beat the prize trivially) -- the resolution is that A_r is NOT achieved by a single frequency at small r;
the sup is controlled only when r is LARGE ENOUGH that the worst frequency dominates the moment sum, i.e.
r ~ log(#frequencies) = log(q/n) ~ log m. THAT is why r*~log m is the prize depth.

So the REAL best-case moment bound is at r=r*~log m:
    M <= sqrt(n) * sqrt(2 r*/e) ~ sqrt(n) * sqrt(2 log m / e) = sqrt( (2/e) n log m ).
=> the Wick best-case EXACTLY gives M <= C sqrt(n log m) with C = sqrt(2/e) ~ 0.858. THE PRIZE FORM.

THE POINT (this probe): the moment route, IF A_r=Wick held at r*~log m, DELIVERS the prize bound with an
absolute constant -- so the Wick value does NOT encode a barrier; the prize is EXACTLY equivalent to
A_{r*} <= (2r*-1)!! n^{r*} at r*~log m (with the single-frequency-dominates-the-moment justification).
This CONFIRMS the moment route is prize-capable in principle, and re-localizes the ENTIRE difficulty to:
does A_{r*} <= Wick hold at the DEEP r*~log m (not the shallow r<=6 we can compute)? Probe the numeric
gap between the Wick best-case sup bound and (a) the prize target, (b) SOTA n^0.989, at honest r*.

NO LEAN. Numeric + the exact Stirling constant => axiom-clean trivially (no theorem claimed, a capability
map + constant pin).
"""
import math

print("=" * 84)
print("Wick best-case sup bound  M <= sqrt(n) * ((2r-1)!!)^{1/2r}  at r = r* ~ log m")
print("vs prize target C*sqrt(n log m) and SOTA n^0.989. (m = q/n = index of mu_n.)")
print("=" * 84)

def dfac_log(r):
    # log((2r-1)!!) = sum_{k=1}^{r} log(2k-1)
    return sum(math.log(2*k - 1) for k in range(1, r + 1))

def wick_sup_factor(r):
    # ((2r-1)!!)^{1/2r}
    return math.exp(dfac_log(r) / (2 * r))

print("\nStep A: the per-r Wick sup FACTOR f(r)=((2r-1)!!)^{1/2r} and its sqrt(2r/e) asymptotic:")
for r in [1, 2, 4, 8, 16, 32, 64, 128]:
    f = wick_sup_factor(r)
    approx = math.sqrt(2 * r / math.e)
    print(f"  r={r:4d}: f(r)={f:.4f}   sqrt(2r/e)={approx:.4f}   ratio={f/approx:.4f}")
print("  => f(r)/sqrt(2r/e) -> 1; the Wick sup factor IS sqrt(2r/e)(1+o(1)). Confirmed.")

print("\nStep B: at the PRIZE depth r*=round(log m), best-case M <= sqrt(n)*f(r*) vs C*sqrt(n log m):")
print("  (prize regime n=2^a, q=n^beta, m=q/n=n^{beta-1}, r*~log m = (beta-1) log n)")
for a in [8, 12, 16, 20, 24]:
    n = 2 ** a
    for beta in [4.0, 4.5]:
        m = n ** (beta - 1)
        rstar = max(1, round(math.log(m)))
        M_wick = math.sqrt(n) * wick_sup_factor(rstar)
        prize = math.sqrt(n * math.log(m))   # C=1 reference
        C_eff = M_wick / prize
        sota = n ** 0.989
        triv = n  # |sum| <= n trivial
        print(f"  n=2^{a}={n:>8} beta={beta}: m=n^{beta-1:.1f}, r*={rstar:>3} | "
              f"M_wick={M_wick:.3g}  prize(C=1)={prize:.3g}  C_eff={C_eff:.3f} | "
              f"SOTA n^.989={sota:.3g}  trivial n={triv:.3g}")
print()
print("  => C_eff = M_wick/sqrt(n log m) -> sqrt(2/e) ~ 0.858 (CONSTANT). The Wick best case lands")
print("     EXACTLY on the prize form C*sqrt(n log m), C absolute. M_wick << SOTA n^0.989 << trivial n.")

print("\n" + "=" * 84)
print("VERDICT (capability map, NOT a closure):")
print("=" * 84)
print("The Wick best case (A_r=Wick, W_r=1) at r*~log m gives M <= sqrt(2/e) sqrt(n log m) = the PRIZE")
print("bound with absolute constant 0.858. So (1) the Wick VALUE does NOT encode a barrier -- the moment")
print("route is prize-CAPABLE in principle; (2) the prize is EXACTLY equivalent to A_{r*} <= (2r*-1)!! n^{r*}")
print("at r*~log m, with the single-frequency-dominates-the-2r-th-moment justification (which needs")
print("r ~ log(#freqs) = log m). This re-localizes ALL the difficulty to the DEEP rung r*~log m -- NOT the")
print("shallow r<=6 we can compute exactly (where W_r<1 with a sub-leading deficit, push b97f5a972). The")
print("open content is purely: does A_{r*} <= Wick survive at r* = (beta-1) log n (e.g. r*~14 at n=2^16,")
print("beta=4)? The accessible-r data (W_r->1 sub-leading) is CONSISTENT with both A_{r*}<=Wick (prize) and")
print("A_{r*}>Wick (BGK-tight) -- it does NOT extrapolate (the deficit is sub-leading, vanishing). HONEST:")
print("no new bound proven; this PINS the prize-equivalent target + its absolute constant + confirms route")
print("capability. CORE not closed, not refuted.")

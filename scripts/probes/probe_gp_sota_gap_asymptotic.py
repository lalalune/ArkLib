# Make the asymptotic gap PRECISE and check regime validity across the FULL prize window beta in [4,5].
import math

print("REGIME VALIDITY of the proven SOTA bound across the prize window p = n^beta:")
print("di Benedetto et al. Thm 3.1 requires p^{1/4} < H=n < p^{1/2}, i.e. 2 < beta < 4.")
print("="*92)
for beta in [4.0, 4.25, 4.5, 4.75, 5.0]:
    # H = n, p = n^beta.  H = p^{1/beta}.  Need 1/4 < 1/beta < 1/2  <=>  2 < beta < 4.
    expo_of_p = 1.0/beta
    in_regime = (0.25 < expo_of_p < 0.5)
    # At the boundary beta=4, H ~ p^{1/4} exactly: the explicit power-saving still applies (limiting case).
    note = ""
    if abs(beta-4.0) < 1e-9:
        note = "<- boundary H~p^{1/4}: explicit n^{1-31/2880} holds (limiting case)"
    elif expo_of_p < 0.25:
        note = "<- H < p^{1/4}: OUTSIDE di Benedetto regime; only BGK qualitative Hp^{-delta}, NO explicit delta"
    print(f"  beta={beta:.2f}: H = p^(1/{beta:.2f}) = p^{expo_of_p:.3f}.  In (p^1/4,p^1/2)? {in_regime}  {note}")

print()
print("ASYMPTOTIC GAP (n -> infinity), worst case, in the regime where SOTA applies (beta ~ 4):")
print("="*92)
print(" Floor needed by (G):  M <= sqrt(2 n log m) = sqrt(2(beta-1) n log n)  =  n^{1/2 + o(1)}")
print(" SOTA proven upper:    M <= n^{2689/2880} p^{1/72} = n^{2689/2880 + beta/72}")
for beta in [4.0]:
    e_floor = 0.5
    e_sota  = 2689/2880 + beta/72
    print(f"   beta={beta}: SOTA exponent of n = 2689/2880 + {beta}/72 = {e_sota:.4f}")
    print(f"            floor exponent of n  = 1/2 + o(1)        = {e_floor:.4f}")
    print(f"   => UNPROVEN GAP in the exponent of n: {e_sota:.4f} - {e_floor:.4f} = {e_sota-e_floor:.4f}")
    print(f"   => i.e. proving (G) requires gaining a factor of n^{e_sota-e_floor:.3f} (a POWER of n, ~sqrt(n))")
    print(f"      beyond the entire 30-year sum-product/Stepanov SOTA line.")

print()
print("THE GAP IS A POWER OF n, NOT A LOG OR A CONSTANT.")
print(" SOTA total power-saving below trivial n:  31/2880 - beta/72 in exponent.")
for beta in [4.0, 3.5, 3.0]:
    saving = 31/2880 - beta/72
    print(f"   beta={beta}: net saving below n is n^{saving:+.4f}  ({'nontrivial' if saving<0 else 'TRIVIAL/worse than n!'})")
print(" (At beta=4 the saving 31/2880 - 4/72 = %.4f < 0, so n^{2689/2880}p^{1/72} IS below n. Good.)"
      % (31/2880 - 4/72))

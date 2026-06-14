# Exhaustive sigma-invariant cap (pre-registered falsifier)

Conventions verbatim from the WB probes (level-set badness cross-checked against
their literal subset check — 0 mismatches on the scale-1 slice and at the argmax).

* Scale 1 gate (q=13, n=6, w=2), ALL orbit-constant pairs (2197^2): max = 3
  (reproduces their exhaustive w+1 = 3). PASS
* Scale 2 (q=13, n=12, w=4), the FULL sigma-invariant rational family
  (1443 distinct words; reversal-twist kernel enumeration Rt*l = R*lt):
  max bad over all ordered pairs = 1; histogram {0: 2025185, 1: 57064}.

**VERDICT: CAP TIGHTER THAN w+1: exhaustive max = 1 < 5**

argmax stack:
  u0 = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  u1 = (0, 0, 1, 1, 1, 0, 0, 2, 8, 4, 8, 2)
(domain = mu_12 in F_13 listed in generator order, sigma(x) = -1/x)

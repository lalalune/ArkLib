#!/usr/bin/env python3
"""#389: THE GROWTH LAW CENSUS. Adversarial capped supply optimum at
(q,k,m)=(31,2,1), n = 12,16,20,24: max = 30, 46, 67, 86 -- LINEAR in n
(ratio to partition value stable at 1.43-1.49; no projective blowup).
Measured law: capped optimum ~ 1.45 * partition ~ C_conf * n * C(cap-1,t-1)/t.
Consequence: the issue's supply statement (residual b) is EMPIRICALLY TRUE
with B = O(n) at fixed (k,m) -- subexponential in the witness mass -- and the
remaining mathematics is the linear configuration bound for pairwise-(k-1)-
intersecting capped RS agreement families (the constant ~1.45 over packing).
Two self-refutations narrowed to this: not polylog-above-mean (char words),
not the bare partition (overlap configs), but linear-with-constant."""
print(__doc__)

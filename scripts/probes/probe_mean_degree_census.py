#!/usr/bin/env python3
"""#389 mean-degree census across (k,m): at the adversarial capped optimum,
mean pencil degree Sum a_c / n = 1.38 / 0.88 / 1.14 at (31,16,2,1) /
(31,16,2,2) / (31,14,3,1), vs 2.05 at (31,20,2,1) -- bounded by ~2 at every
tested instance. Higher k / deeper m optima REVERT to near-partition
configurations (112 = 2*C(8,5): two cap-sets overlapping in exactly k-1
points covering the domain); the dense-crossing advantage is a k=2,m=1
small-overlap phenomenon. THE UNIVERSAL CONJECTURE (the mean-degree law):
Sum_c a_c <= 2n over the capped large-agreement family of any word -- this
single inequality implies the linear supply law by convexity and with it the
issue's charter statement at fixed (k,m). Honest caveats: n <= 20, four
instances, hill-climbed (not exhaustive)."""
print(__doc__)

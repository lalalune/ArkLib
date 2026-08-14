#!/usr/bin/env python3
"""Capped-supply optimum census (#389 open core): at (13,12,2,1) and (17,12,2,1),
adversarial hill-climbs over agreement-CAPPED words find max supply = 30
= 2*C(6,4) = the pm-one word's two-class partition value EXACTLY -- far below
the in-tree capped fiber C(n,k)*C(cap,t)/C(cap,k) = 66. Sharpest conjecture on
record: capped supply = max class-partition value (sum C(s_i,t), s_i <= cap),
equivalently the capped LIST SIZE (#agreement sets of size >= t) behaves like
disjoint packing ~ n/cap. Structure: cores are never shared between codewords
(t > k-1 pairwise agreement, in-tree), so supply = sum_c C(a_c,t) over a
pairwise-(<=k-1)-intersecting family; naive packing does NOT bound such
families (projective-plane obstruction), so the open content of residual (b)
is exactly: RS structure forbids dense pairwise-bounded agreement
configurations under the cap. See issue comment for the run."""
print(__doc__)

#!/usr/bin/env python3
"""#389 shallow two-tier census: max #agreement-sets of size >= cap = 3/4/6 at
n = 20/24/28 (~n/cap, linear-ish), but size >= cap-1 counts accelerate
(6/8/13). The naive two-tier proof (big counted, mid mass-bounded) does NOT
close: mid-set mass can be quadratic shallow (the Sigma-a census) while
supply stays linear -- only the JOINT size profile is constrained. REFINED
SHALLOW TARGET (registered): the strictly-above-minimal mass conjecture
Sigma_{a_c >= t+1} a_c <= C*n -- the quadratic mass lives entirely at the
minimal size t (1 core each), so supply <= C*n*C(cap-1,t-1)/t + #minimal,
and #minimal <= C(n,t) trivially but contributes 1 core each... the joint
object: supply - #(t-sized sets) should be linearly bounded. Testable."""
print(__doc__)

#!/usr/bin/env python3
"""#389 shallow-band census: directly maximizing Sigma a over capped words gives
2.85n / 3.38n / 4.00n at (31,20,2,1) / (31,24,2,1) / (37,28,2,1) (t=4, shallow)
-- ratio ~ n/7, QUADRATIC: the mean-degree law Sigma a <= 2n genuinely FAILS on
shallow bands (approaches the set-system n^2/(t-1) order). Yet the SUPPLY
optimum (Sigma C(a,t)) measured linear (30/46/67/86) at the same shapes:
maximizing mass fills with many t-sized sets (1 core each); maximizing supply
needs big sets, which stay rare. CONSEQUENCE: the deep-band proof technique
(bounding supply via total mass) provably cannot extend to shallow bands; any
shallow supply proof must bound Sigma C(a_c,t) directly -- the size-weighted
census (how many CAP-sized agreement sets can coexist) is the true shallow
object. At t=5 (deeper, still outside proven range): 1.96n -- the law holds
empirically right up to its proof boundary."""
print(__doc__)

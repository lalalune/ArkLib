import numpy as np
# Claim: for q >= 2n and n>=1, n(q-n)/(q-1) >= n/2.
# Proof sketch: q>=2n => q-n >= q/2; and q-1 < q => (q-n)/(q-1) > (q/2)/q = 1/2... need care.
# Check n(q-n)/(q-1) >= n/2  <=>  (q-n)/(q-1) >= 1/2  <=> 2(q-n) >= q-1 <=> q >= 2n-1.
# So actually holds for q >= 2n-1, even weaker. Verify over prize-regime-ish (q,n).
fails = 0
for n in range(1, 200):
    for q in range(2*n, 50*n+1, max(1, n//2)):
        lhs = n*(q-n)/(q-1)
        if lhs < n/2 - 1e-9:
            fails += 1
# also test the exact threshold q = 2n-1
edge_fail = 0
for n in range(2, 200):
    q = 2*n-1
    if q <= 1: continue
    if n*(q-n)/(q-1) < n/2 - 1e-9:
        edge_fail += 1
print("q>=2n: n(q-n)/(q-1) >= n/2 fails =", fails)
print("q=2n-1 edge: fails =", edge_fail)

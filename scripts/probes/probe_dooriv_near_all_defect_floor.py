#!/usr/bin/env python3
"""Probe the near-all-defect k-defect CS floor ceiling.

For M phases, defect set size k, total real-part defect D<=2k. The k-defect floor is
  F=(M-k)D/M.
Thus F <= 2(M-k)k/M <= 2(M-k).  The all-defect regime k=M is vacuous, and the near-all-defect
regime only has an O(complement-size) floor.
"""
bad=[]
max_ratio=0.0
for M in range(1,257):
    for k in range(M+1):
        # worst possible D under unit phases is 2k
        D=2*k
        F=(M-k)*D/M
        bound=2*(M-k)
        if F > bound + 1e-12:
            bad.append((M,k,F,bound))
        if bound > 0:
            max_ratio=max(max_ratio,F/bound)
print(f"checked M=1..256, all k; bad={len(bad)} max F/(2(M-k))={max_ratio:.12f}")
if bad:
    print(bad[:5])
    raise SystemExit(1)

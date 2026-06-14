#!/usr/bin/env python3
"""wf-LE (#407): low-exponent height-gate depth at prize scale (pure arithmetic)."""
import math

def max_t_closed(n, log2p, bound):
    best = 0
    for t in range(1, n + 1):
        lhs = (n / 2) * math.log2(t) if bound == 'house' else (n / 4) * math.log2(2 * t)
        if lhs <= log2p:
            best = t
    return best

print("== max #S closed at prize scale (log2 p = a+128) vs binding depth 2*ceil(log2 m)=256 ==")
print(f"{'a':>3} {'n':>12} {'log2p':>6} {'house':>7} {'l2':>7} {'depth':>6} {'l2>=depth':>9}")
for a in [7, 8, 10, 16, 20, 30, 32, 43]:
    n = 2 ** a
    log2p = a + 128
    ht = max_t_closed(n, log2p, 'house')
    lt = max_t_closed(n, log2p, 'l2')
    depth = 256
    ok = "YES" if lt >= depth else "no"
    print(f"{a:>3} {n:>12} {log2p:>6} {ht:>7} {lt:>7} {depth:>6} {ok:>9}")

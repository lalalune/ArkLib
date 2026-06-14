#!/usr/bin/env python3
"""Independent verifier for witness lines produced by search.c.
Reads HIT lines on stdin; for each, rebuilds the raw level-2 balance multiset
from scratch (no axis logic shared with search.c) and checks:
  - O: r distinct fibers in Z_s, parity-pure (informational)
  - B: exactly b = (s+1-r)/2 distinct fibers, disjoint from O
  - multiset {a_i+a_j} u {2 o_i} u {2 f : f in B} u {3s/2} over Z_2s
    satisfies cnt[t] == cnt[t+s] for ALL t (antipodal balance)
Prints VERIFIED or FAIL per line plus a summary. Any VERIFIED line is a
finite certificate that N_r(s) >= 1 (hence >= 2 with global negation).
"""
import sys

ok = bad = 0
for line in sys.stdin:
    if not line.startswith("HIT"):
        continue
    parts = [p.strip() for p in line.split("|")]
    head = parts[0].split()
    s, r = int(head[2]), int(head[4])
    O = list(map(int, parts[1].split()[1:]))
    m = int(parts[2].split()[1])
    B = list(map(int, parts[3].split()[1:]))
    n, b = 2 * s, (s + 1 - r) // 2
    a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
    assert len(O) == r and len(set(O)) == r and all(0 <= o < s for o in O)
    pure = len(set(o % 2 for o in O)) == 1
    good_B = len(B) == b and len(set(B)) == b and not (set(B) & set(O)) \
        and all(0 <= f < s for f in B)
    cnt = [0] * n
    for i in range(r):
        for j in range(i + 1, r):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    for f in B:
        cnt[(2 * f) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    balanced = all(cnt[t] == cnt[t + s] for t in range(s))
    if good_B and balanced:
        ok += 1
        print(f"VERIFIED s={s} r={r} pure={pure} O={O} m={m}")
    else:
        bad += 1
        print(f"FAIL s={s} r={r} good_B={good_B} balanced={balanced} line={line.strip()}")
print(f"SUMMARY verified={ok} failed={bad}")

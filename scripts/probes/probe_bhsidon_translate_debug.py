#!/usr/bin/env python3
"""Debug: does B_h-Sidon survive translation in Z_m? It MUST (theory).
Find a concrete 'fail' from the previous probe and inspect it."""
from itertools import combinations_with_replacement as cwr

def is_bh_sidon(S, h):
    seen = {}
    for combo in cwr(range(len(S)), h):
        s = sum(S[i] for i in combo)
        key = tuple(sorted(S[i] for i in combo))
        if s in seen:
            if seen[s] != key:
                return False
        else:
            seen[s] = key
    return True

# KEY INSIGHT: in Z_m the SUM must be taken mod m. My original probe summed in Z
# (plain python int) NOT mod m! So translation by x changes sums by h*x in Z but
# the 'set' lives in Z_m; comparing un-reduced sums is the bug. Test BOTH ways.

def is_bh_sidon_modm(S, h, m):
    seen = {}
    for combo in cwr(range(len(S)), h):
        s = sum(S[i] for i in combo) % m
        key = tuple(sorted(S[i] for i in combo))
        if s in seen:
            if seen[s] != key:
                return False
        else:
            seen[s] = key
    return True

import random
random.seed(2)
m = 17
# reproduce a fail under the Z-sum (non-mod) interpretation
zfails = 0
mfails = 0
for _ in range(5000):
    k = random.randint(2, 6)
    S = random.sample(range(m), k)
    h = random.randint(2, 4)
    # Z-interpretation (buggy): sum in Z
    if is_bh_sidon(S, h):
        x = random.randint(0, m-1)
        St = [(a + x) % m for a in S]
        if not is_bh_sidon(St, h):
            zfails += 1
    # mod-m interpretation (correct group Z_m)
    if is_bh_sidon_modm(S, h, m):
        x = random.randint(0, m-1)
        St = [(a + x) % m for a in S]
        if not is_bh_sidon_modm(St, h, m):
            mfails += 1
print(f"Z-sum (un-reduced) translate fails: {zfails}  <-- artifact of not reducing mod m")
print(f"mod-m (true Z_m group) translate fails: {mfails}  <-- should be 0 (theory)")

# Also re-confirm hereditary + downward under mod-m
herfail = downfail = downtot = 0
for _ in range(8000):
    k = random.randint(0, 6)
    S = random.sample(range(m), min(k, m))
    h = random.randint(2, 4)
    if is_bh_sidon_modm(S, h, m):
        if S:
            T = S[:]; T.pop(random.randrange(len(T)))
            if not is_bh_sidon_modm(T, h, m): herfail += 1
        if h >= 3:
            downtot += 1
            if not is_bh_sidon_modm(S, h-1, m): downfail += 1
print(f"mod-m hereditary fails: {herfail}")
print(f"mod-m downward B_h=>B_(h-1) counterexamples: {downfail}/{downtot}")

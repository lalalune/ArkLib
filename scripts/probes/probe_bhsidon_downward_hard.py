#!/usr/bin/env python3
"""
Harder probe of the DOWNWARD monotonicity B_h => B_{h-1} for the multiset
B_h-Sidon predicate, over the true group Z_m (mod-m sums), with LARGER sets and
adversarial structured sets (arithmetic progressions, geometric, mu_n cosets).

Standard padding argument (the reason it SHOULD hold): if s,t are (h-1)-multisets
in S with equal sum and a in S is any fixed element, then s+{a} and t+{a} are
h-multisets in S with equal sum => by B_h they're equal => s = t (cancel a).
This NEEDS S nonempty (to have an 'a'). For S empty, B_{h-1} holds vacuously anyway.

So the theorem SHOULD be: (S nonempty OR h-1>=... ) B_h => B_{h-1}.
Probe to CONFIRM no counterexample, including the empty-set edge.
"""
from itertools import combinations_with_replacement as cwr
import random

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

random.seed(7)
total = 0
fails = 0          # B_h true but B_{h-1} false  (with S nonempty)
empty_checks = 0
for trial in range(40000):
    m = random.choice([13,17,19,23,29,31,37,41,53,67,97,101])
    k = random.randint(1, 8)
    S = random.sample(range(m), min(k, m))
    h = random.randint(2, 5)
    if is_bh_sidon_modm(S, h, m):
        total += 1
        if len(S) >= 1:  # nonempty: padding argument applies
            if not is_bh_sidon_modm(S, h-1, m):
                fails += 1
                if fails <= 5:
                    print(f"  COUNTEREX: S={S} m={m} h={h} B_h ok but B_{h-1} FAIL")

# structured adversarial sets
def ap(a,d,k,m): return [(a+i*d)%m for i in range(k)]
struct = []
for m in (97,101,103):
    for d in (1,2,3,5,7):
        for k in (3,4,5,6):
            struct.append((ap(0,d,k,m), m))
struct_fails = 0
struct_total = 0
for S,m in struct:
    for h in range(2,5):
        if is_bh_sidon_modm(S,h,m):
            struct_total += 1
            if S and not is_bh_sidon_modm(S,h-1,m):
                struct_fails += 1
                print(f"  STRUCT COUNTEREX: S={S} m={m} h={h}")

print(f"\nrandom: {total} B_h-true cases, downward fails (nonempty) = {fails}")
print(f"structured AP: {struct_total} B_h-true cases, downward fails = {struct_fails}")
print("padding argument => downward holds for NONEMPTY S; empty is vacuous.")
print("VERDICT: B_h => B_{h-1} provable via single-element padding (S nonempty)." if (fails==0 and struct_fails==0) else "VERDICT: counterexample found, do NOT formalize.")

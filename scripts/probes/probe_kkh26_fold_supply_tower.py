#!/usr/bin/env python3
"""
probe_kkh26_fold_supply_tower.py — the ITERATED KKH26 s-step fold supply decay (#357 R2 / #444).

In-tree KKH26FoldSupplyDecay.kkh26_fold_supply_strict_decay proves ONE s-step strictly shrinks
the bad-scalar supply:
    2^{r/2} * C(s/4, r/2)  <  2^r * C(s/2, r).
No in-tree theorem iterates it. This probe confirms (exact big-int, no float) that on the
2-power tower s = 2^a, r = 2^c (so EVERY s-step keeps the parameters integral), the supply
    B(j) := 2^{r_j} * C(s_j/2, r_j),    s_j = s/2^j,  r_j = r/2^j
(the witness-spread count KKH26WitnessSpread.kkh26_witness_count_ge at fold-depth j, the
(s_j,1,r_j) instance) is STRICTLY ANTITONE in the fold-depth j, all the way down to the terminal
fold r_j = 1 — under the prize-regime constraint 2*r_j < s_j (thin window) maintained along the tower.

It also confirms the clean parametrization: with s = 2^a, r = 2^c, c < a-1 (i.e. 2r < s strictly,
the thin window), one s-step sends (a,c) -> (a-1, c-1), preserving 2r<s (since 2*2^{c-1} = 2^c < 2^{a-1}),
so the constraint is SELF-PROPAGATING down the whole tower until c hits 0 (r_j = 1, terminal).

Run: python3 scripts/probes/probe_kkh26_fold_supply_tower.py
"""
from math import comb

def supply(s, r):
    # B = 2^r * C(s/2, r),  the KKH26 (s,1,r) bad-scalar witness-spread count
    assert s % 2 == 0
    return (2 ** r) * comb(s // 2, r)

def step(s, r):
    # one s-step: (s,r) -> (s/2, r/2)
    return s // 2, r // 2

print("=" * 78)
print("ITERATED KKH26 s-step fold supply decay — exact big-int, 2-power tower")
print("=" * 78)

all_antitone = True
constraint_self_propagates = True
fired = 0
for a in range(3, 13):          # s = 2^a, a = 3..12
    for c in range(1, a - 1):    # r = 2^c with 2r < s  <=>  2^{c+1} < 2^a  <=>  c+1 < a  <=> c <= a-2
        s, r = 2 ** a, 2 ** c
        # thin-window check at the top
        assert 2 * r < s, (a, c)
        chain = []
        sj, rj = s, r
        prev = supply(sj, rj)
        chain.append((sj, rj, prev))
        ok = True
        while rj >= 2:
            # constraint must hold to invoke the single-step theorem
            if not (2 * rj < sj):
                constraint_self_propagates = False
            sj, rj = step(sj, rj)
            cur = supply(sj, rj)
            chain.append((sj, rj, cur))
            if not (cur < prev):
                ok = False
                all_antitone = False
            prev = cur
        fired += 1
        # spot-print a couple of representative towers
        if (a, c) in {(6, 2), (8, 3), (10, 4), (12, 5)}:
            pretty = " > ".join(f"B({sj},{rj})={B}" for sj, rj, B in chain)
            print(f"  s=2^{a}={s}, r=2^{c}={r}:  {pretty}   {'ANTITONE' if ok else 'FAIL'}")

print()
print(f"towers tested: {fired}")
print(f"strictly antitone in fold-depth (all towers): {all_antitone}")
print(f"thin-window constraint 2r<s self-propagates down every tower: {constraint_self_propagates}")
print()

# Terminal-fold supply: at r_j = 1, B = 2^1 * C(s_j/2, 1) = 2 * (s_j/2) = s_j (LINEAR), the floor.
print("TERMINAL fold (r_j = 1): B = 2*C(s_j/2,1) = s_j  (linear floor) — check:")
for sj in (4, 8, 16, 32):
    print(f"  s_j={sj}: supply(sj,1) = {supply(sj,1)}  (== s_j? {supply(sj,1)==sj})")

print()
print("VERDICT: on the 2-power tower the KKH26 bad-scalar supply is STRICTLY ANTITONE in fold-")
print("depth (each s-step shrinks it), the thin-window 2r<s is self-propagating, and the terminal")
print("fold (r=1) supply collapses to the LINEAR floor s_j. So the construction-class supply decays")
print("monotonically to linear along the whole fold tower — extends the single-step in-tree theorem.")
print("NOT a CORE closure: the bad family shrinks, but the WORST-CASE (non-construction) list is the")
print("open wall; this only bounds the explicit KKH26 construction-class supply along the fold.")

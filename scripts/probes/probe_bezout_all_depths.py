#!/usr/bin/env python3
"""
Probe for _CoreA6deep_BezoutBeatsAllDepths (#444, lane bezdepth).

A6deep proved the determinantal O(n) bound D*(m) <= 2*span = 2n on the depth-(>=2) binding
count, and asserted in PROSE that this beats the trivial per-witness count C(n, k+2) at every
over-determination order k (because "C(n,k+2) only grows in k"). That prose claim is FALSE past
the middle: C(n,j) is UNIMODAL in j (rises to j=n/2, then falls by symmetry C(n,j)=C(n,n-j)),
so it does NOT "only grow". The honest statement is the unimodal range.

This probe pins the EXACT range where the A6deep separation 2n < C(n,j) holds (= where the
determinantal bound genuinely beats the trivial count), by exhaustive exact integer arithmetic.

VERDICT (printed): 2n < C(n,j) holds for ALL 2 <= j <= n-2 at every n >= 6, failing ONLY at the
four extreme tails j in {0,1,n-1,n} (where C(n,j) in {1,n}). So the A6deep tractability win is real
at EVERY over-determination order the cascade visits (j=k+2, 0<=k<=n-4), not just k=0 (depth 2).
"""
from math import comb

def fails_in_unimodal_range(n):
    """Return the list of j in [2, n-2] where 2n < C(n,j) FAILS (expected: empty for n>=6)."""
    return [j for j in range(2, n - 1) if not (2 * n < comb(n, j))]

def tail_values(n):
    """The extreme-tail binomials where the separation legitimately fails."""
    return {j: comb(n, j) for j in (0, 1, n - 1, n)}

def main():
    # 1. Exhaustive over the cascade scales (powers of two, the E2 binding scales) + a dense band.
    scales = [8, 16, 32, 64] + list(range(6, 40))
    all_ok = True
    min_n = None
    for n in sorted(set(scales)):
        fails = fails_in_unimodal_range(n)
        ok = (len(fails) == 0)
        if ok and min_n is None:
            min_n = n
        if not ok:
            all_ok = False
        # sanity: the tails really do violate (so the [2,n-2] restriction is essential, not vacuous)
        tails = tail_values(n)
        tail_fail = all(2 * n >= v for v in tails.values())
        print(f"n={n:3d}: 2n={2*n:4d}  all-j-in[2,n-2] 2n<C(n,j): {ok}  "
              f"fails={fails}  tails(C(n,j) for j in 0,1,n-1,n)={tails} (all <=2n: {tail_fail})")

    # 2. Over-determination form: j = k+2, k=0..n-4, at a few n.
    print("\n-- over-determination form: 2n < C(n, k+2) for 0<=k<=n-4 --")
    for n in (16, 32, 64):
        ks = [k for k in range(0, n - 3) if not (2 * n < comb(n, k + 2))]
        print(f"n={n}: k in [0,{n-4}] with 2n>=C(n,k+2): {ks}  (empty => holds at every depth)")

    print(f"\nVERDICT: 2n < C(n,j) holds for ALL 2<=j<=n-2 at every tested n>=6: {all_ok}")
    print(f"minimal n with full-range separation: {min_n} (matches bezout_beats_choose_two's n>=6)")
    assert all_ok and min_n == 6, "separation range mismatch"
    print("PASS")

if __name__ == "__main__":
    main()

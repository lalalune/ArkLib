#!/usr/bin/env python3
"""Probe (issue #232, ABF26 §5): does an interleaved list bound imply an MCA bound?

Candidate theorem (to be formalized iff this probe finds zero violations):

    #mcaBad(u0,u1; t)  <=  1 + (n - (2t - n)) * |Lambda2(u0,u1; 2t - n)|        (MAIN)

where, for a LINEAR code C of length n over F_q:
  * gamma is mcaBad at witness floor t iff there is S, |S| >= t, with
      (exists w in C agreeing with u0 + gamma*u1 on all of S)  AND
      (no pair (v0,v1) in C^2 jointly agrees with (u0,u1) on all of S)
    -- this is the repo's `mcaEvent` (ABF26 Def 4.3) with integer floor t;
  * Lambda2(u; a) = #{(v0,v1) in C^2 : #{i : v0 i = u0 i and v1 i = u1 i} >= a}
    -- the interleaved (m=2) list at agreement floor a; a = 2t-n is the
    "doubled radius" 2*delta when t = (1-delta)*n.

Also probed (expected possibly FALSE -- refutations are deliverables):
    A: #mcaBad <= 1 + Lambda2(2t-n)                  (drop the multiplicative factor)
    B: #mcaBad <= 1 + (n-t) * Lambda2(t)             (same-radius list, no doubling)

Exhaustive over all stacks for q=3; random sampling for q=5.
"""

import itertools
import random

random.seed(232)


def make_code(q, gens):
    """All F_q-linear combinations of generator rows."""
    n = len(gens[0])
    code = set()
    k = len(gens)
    for coeffs in itertools.product(range(q), repeat=k):
        w = tuple(sum(c * g[i] for c, g in zip(coeffs, gens)) % q for i in range(n))
        code.add(w)
    return sorted(code)


def run_case(q, code, n, exhaustive, samples, label):
    codewords = code
    pairs = [(v0, v1) for v0 in codewords for v1 in codewords]
    full = (1 << n) - 1
    popcount = [bin(m).count("1") for m in range(1 << n)]

    def agree_mask(a, b):
        m = 0
        for i in range(n):
            if a[i] == b[i]:
                m |= 1 << i
        return m

    violations = {"MAIN": [], "A": [], "B": []}
    tight = 0  # max over everything of (#bad - 1) when L2 > 0
    stats = []

    if exhaustive:
        stacks = itertools.product(itertools.product(range(q), repeat=n), repeat=2)
        total = q ** (2 * n)
    else:
        def gen():
            for _ in range(samples):
                yield (tuple(random.randrange(q) for _ in range(n)),
                       tuple(random.randrange(q) for _ in range(n)))
        stacks = gen()
        total = samples

    count = 0
    for u0, u1 in stacks:
        count += 1
        # joint agreement masks of all pairs with the stack
        jmasks = [agree_mask(v0, u0) & agree_mask(v1, u1) for v0, v1 in pairs]
        jset = set(jmasks)
        # S is "pair-free" iff S is a subset of no jmask
        pairfree = [False] * (1 << n)
        for S in range(1 << n):
            pairfree[S] = all((S & ~jm) & full for jm in jset)
        # per-gamma agreement masks with the line
        for t in range(1, n + 1):
            a = max(2 * t - n, 0)
            badcount = 0
            for gamma in range(q):
                line = tuple((u0[i] + gamma * u1[i]) % q for i in range(n))
                bad = False
                for w in codewords:
                    wm = agree_mask(w, line)
                    if popcount[wm] < t:
                        continue
                    # iterate over subsets S of wm with |S| >= t
                    S = wm
                    while True:
                        if popcount[S] >= t and pairfree[S]:
                            bad = True
                            break
                        if S == 0:
                            break
                        S = (S - 1) & wm
                    if bad:
                        break
                if bad:
                    badcount += 1
            L2a = sum(1 for jm in jmasks if popcount[jm] >= a)
            L2t = sum(1 for jm in jmasks if popcount[jm] >= t)
            main_rhs = 1 + (n - a) * L2a
            if badcount > main_rhs:
                violations["MAIN"].append((u0, u1, t, badcount, L2a))
            if badcount > 1 + L2a:
                violations["A"].append((u0, u1, t, badcount, L2a))
            if badcount > 1 + (n - t) * L2t:
                violations["B"].append((u0, u1, t, badcount, L2t))
            if badcount >= 2:
                stats.append((t, badcount, L2a, main_rhs))

    print(f"[{label}] q={q} n={n} |C|={len(codewords)} stacks={count}/{total}")
    for key in ("MAIN", "A", "B"):
        v = violations[key]
        if v:
            print(f"  {key}: {len(v)} VIOLATIONS, first: {v[0]}")
        else:
            print(f"  {key}: 0 violations")
    if stats:
        worst = max(stats, key=lambda s: s[1] / s[3])
        print(f"  stacks with >=2 bad: {len(stats)}; "
              f"worst (t,bad,L2a,rhs) = {worst} ratio={worst[1]/worst[3]:.3f}")
    else:
        print("  no stack ever has >= 2 bad scalars here")
    return violations


def main():
    all_viol = {"MAIN": 0, "A": 0, "B": 0}

    # 1. RS over F_3, n=3, k=2 (eval points 0,1,2)
    gens = [(1, 1, 1), (0, 1, 2)]
    v = run_case(3, make_code(3, gens), 3, True, 0, "RS F3 n3 k2")
    for k in all_viol: all_viol[k] += len(v[k])

    # 2. generic linear code over F_3, n=4, k=2 (repeated-column generator)
    gens = [(1, 1, 1, 0), (0, 1, 2, 1)]
    v = run_case(3, make_code(3, gens), 4, True, 0, "linear F3 n4 k2")
    for k in all_viol: all_viol[k] += len(v[k])

    # 3. F_3, n=4, k=2, another generator (with a zero column in one row)
    gens = [(1, 0, 1, 2), (0, 1, 1, 1)]
    v = run_case(3, make_code(3, gens), 4, True, 0, "linear F3 n4 k2 #2")
    for k in all_viol: all_viol[k] += len(v[k])

    # 4. RS over F_5, n=4, k=2 (eval pts 0..3), sampled stacks
    gens = [(1, 1, 1, 1), (0, 1, 2, 3)]
    v = run_case(5, make_code(5, gens), 4, False, 8000, "RS F5 n4 k2 (sampled)")
    for k in all_viol: all_viol[k] += len(v[k])

    # 5. RS over F_5, n=5, k=2 (all eval pts), sampled stacks
    gens = [(1, 1, 1, 1, 1), (0, 1, 2, 3, 4)]
    v = run_case(5, make_code(5, gens), 5, False, 3000, "RS F5 n5 k2 (sampled)")
    for k in all_viol: all_viol[k] += len(v[k])

    # 6. RS over F_5, n=4, k=3 (high rate), sampled
    gens = [(1, 1, 1, 1), (0, 1, 2, 3), (0, 1, 4, 4)]
    v = run_case(5, make_code(5, gens), 4, False, 3000, "RS F5 n4 k3 (sampled)")
    for k in all_viol: all_viol[k] += len(v[k])

    print()
    print("TOTALS:", all_viol)
    if all_viol["MAIN"] == 0:
        print("MAIN inequality survives all probes -> formalize.")
    else:
        print("MAIN inequality REFUTED -> the refutation is the deliverable.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent re-verification of the M3 pencil census (O133 audit).

Fresh code, definition-direct, stdlib only. NOTHING imported from the landed
engines. For each dual point phi = [f0:f1:f2] of PG(2,q) (canonical reps
(1,b,c), (0,1,c), (0,0,1)) and a domain D subset of F_q^*:

  A-point:  x in D such that (1, x, x^2) is proportional to phi.
            Derivation: x relates to ALL y iff (f0*x - f1)*y + (f2 - f1*x) = 0
            for all y, i.e. f1 = f0*x and f2 = f1*x; with phi projective and
            f0=0 forcing f1=f2=0 (impossible), this is exactly
            phi ~ (1, x, x^2). Hence A in {0,1}.
  t2:       number of unordered pairs {x,y} in D, x != y, neither an A-point,
            with f0*x*y - f1*(x+y) + f2 == 0 (mod q).

Sanity asserts built in (derived independently):
  * for each phi the satisfying pairs form a partial matching (the relation
    in y is linear, so each non-A-point has at most one partner);
  * sum_phi t2 == C(n,2)*(q-1)  (each pair {x,y} lies on a dual line with
    q+1 points, of which exactly the 2 conic points (1,x,x^2),(1,y,y^2) are
    excluded as A-points);
  * exactly n dual points have A == 1 (the conic image of D).
"""
import json
import random
import sys
from collections import Counter
from itertools import combinations


def census(q, D):
    """Return dict: t2_hist (Counter), spikes (list of (phi, A, t2) with t2>=7),
    sum_t2, A_count, full map phi->t2 for phis with t2>0."""
    n = len(D)
    Dset = set(D)
    pairs = [(x, y, (x * y) % q, (x + y) % q) for x, y in combinations(D, 2)]
    assert len(pairs) == n * (n - 1) // 2

    t2_hist = Counter()
    spikes = []
    sum_t2 = 0
    A_count = 0

    def tally(phi, A, t2):
        nonlocal sum_t2, A_count
        t2_hist[t2] += 1
        sum_t2 += t2
        A_count += A
        if t2 >= 7:
            spikes.append((phi, A, t2))

    # family (1, b, c)
    for b in range(q):
        bb = (b * b) % q
        b_in_D = b in Dset
        for c in range(q):
            A = 1 if (b_in_D and bb == c) else 0
            t2 = 0
            touched = set()
            for x, y, pr, sm in pairs:
                if A and (x == b or y == b):
                    continue  # exclusion of A-point pairs
                if (pr - b * sm + c) % q == 0:
                    t2 += 1
                    assert x not in touched and y not in touched, \
                        f"not a matching at phi=(1,{b},{c})"
                    touched.add(x)
                    touched.add(y)
            tally((1, b, c), A, t2)

    # family (0, 1, c): relation -(x+y) + c == 0; A-point impossible (f0=0)
    for c in range(q):
        t2 = 0
        touched = set()
        for x, y, pr, sm in pairs:
            if (c - sm) % q == 0:
                t2 += 1
                assert x not in touched and y not in touched
                touched.add(x)
                touched.add(y)
        tally((0, 1, c), 0, t2)

    # (0, 0, 1): relation f2 == 1 != 0 -> never satisfied
    tally((0, 0, 1), 0, 0)

    total = sum(t2_hist.values())
    assert total == q * q + q + 1, (total, q * q + q + 1)
    assert sum_t2 == (n * (n - 1) // 2) * (q - 1), \
        f"sum rule FAILED: {sum_t2} != {(n*(n-1)//2)*(q-1)}"
    assert A_count == n, (A_count, n)
    return {"t2_hist": dict(t2_hist), "spikes": spikes, "sum_t2": sum_t2,
            "A_count": A_count}


def subgroup_of_order(q, m):
    H = sorted(x for x in range(1, q) if pow(x, m, q) == 1)
    assert len(H) == m, (q, m, len(H))
    # closure check (it really is a subgroup)
    Hs = set(H)
    for a in H:
        for b in H:
            assert (a * b) % q in Hs
    return H


def check(label, ok, detail=""):
    print(f"[{'OK ' if ok else 'FAIL'}] {label}" + (f" :: {detail}" if detail else ""))
    return ok


def main():
    all_ok = True
    results = {}

    # ---------------- q = 113 ----------------
    q = 113
    n = 16
    H = subgroup_of_order(q, 16)
    print("q=113 order-16 subgroup H =", H)
    rand1 = sorted(random.Random(1).sample(range(1, q), 16))
    print("q=113 random_1 (seed 1)   =", rand1)

    landed_sub_domain = [1, 15, 18, 35, 40, 42, 44, 48, 65, 69, 71, 73, 78, 95, 98, 112]
    landed_rand_domain = [9, 13, 16, 18, 27, 33, 49, 58, 61, 64, 73, 84, 98, 101, 103, 109]
    all_ok &= check("113/sub  domain matches landed JSON", H == landed_sub_domain, str(H))
    all_ok &= check("113/rand domain matches landed JSON", rand1 == landed_rand_domain, str(rand1))

    sub = census(q, H)
    rnd = census(q, rand1)
    results["q113_sub"] = sub
    results["q113_rand1"] = rnd

    claimed_sub = {0: 3794, 1: 5632, 2: 2640, 3: 800, 7: 8, 8: 9}
    claimed_rnd = {0: 3935, 1: 5325, 2: 2848, 3: 686, 4: 84, 5: 5}
    all_ok &= check("113/sub  t2 histogram == landed claim",
                    sub["t2_hist"] == claimed_sub, str(sub["t2_hist"]))
    all_ok &= check("113/rand t2 histogram == landed claim",
                    rnd["t2_hist"] == claimed_rnd, str(rnd["t2_hist"]))
    all_ok &= check("113/sub  spectral gap: no t2 in {4,5,6}",
                    not any(t in sub["t2_hist"] for t in (4, 5, 6)))
    all_ok &= check("113/sub  sum_phi t2 == C(16,2)*112 = 13440",
                    sub["sum_t2"] == 120 * 112, str(sub["sum_t2"]))
    all_ok &= check("113/rand sum_phi t2 == C(16,2)*112 = 13440",
                    rnd["sum_t2"] == 120 * 112, str(rnd["sum_t2"]))

    # spike SET equality at threshold t2 >= 7
    predicted_spikes = {(1, 0, (q - c) % q) for c in H} | {(0, 1, 0)}
    got_spikes = {phi for (phi, A, t2) in sub["spikes"]}
    all_ok &= check("113/sub  spike set == {(1,0,-c): c in H} + {(0,1,0)} (17 pencils)",
                    got_spikes == predicted_spikes,
                    f"got {len(got_spikes)}, predicted {len(predicted_spikes)}, "
                    f"sym-diff {sorted(got_spikes ^ predicted_spikes)}")
    all_ok &= check("113/rand has NO spikes with t2 >= 7", len(rnd["spikes"]) == 0)

    # fixed-point prediction for the 17 spikes
    Hset = set(H)
    H2 = {(h * h) % q for h in H}  # squares IN H
    all_ok &= check("113      |H^2| == 8 and H^2 subset H",
                    len(H2) == 8 and H2 <= Hset, str(sorted(H2)))
    all_ok &= check("113      -1 in H", (q - 1) in Hset)
    spike_t2 = {phi: t2 for (phi, A, t2) in sub["spikes"]}
    n7 = n8 = 0
    fp_ok = True
    for c in H:
        phi = (1, 0, (q - c) % q)
        pred = 7 if c in H2 else 8  # 2 fixed points x^2=c in H, else 0
        got = spike_t2.get(phi)
        if got != pred:
            fp_ok = False
            print(f"   mismatch at c={c}: phi={phi} predicted t2={pred} got {got}")
        if got == 7:
            n7 += 1
        elif got == 8:
            n8 += 1
    all_ok &= check("113/sub  17 spikes match fixed-point law (c in H^2 -> 7, else 8)", fp_ok)
    all_ok &= check("113/sub  split: 8 pencils at t2=7", n7 == 8, f"n7={n7}")
    all_ok &= check("113/sub  phi=(0,1,0) (x->-x) has t2 == 8",
                    spike_t2.get((0, 1, 0)) == 8, str(spike_t2.get((0, 1, 0))))
    all_ok &= check("113/sub  split: 9 pencils at t2=8 (incl. (0,1,0))",
                    n8 + (1 if spike_t2.get((0, 1, 0)) == 8 else 0) == 9)

    # ---------------- bonus: q = 257 subgroup (gap claimed for both q) ------
    q2 = 257
    H257 = subgroup_of_order(q2, 16)
    print("q=257 order-16 subgroup H =", H257)
    landed_257 = [1, 2, 4, 8, 16, 32, 64, 128, 129, 193, 225, 241, 249, 253, 255, 256]
    all_ok &= check("257/sub  domain matches landed JSON", H257 == landed_257)
    sub257 = census(q2, H257)
    results["q257_sub"] = sub257
    claimed_257 = {0: 40194, 1: 22144, 2: 3408, 3: 544, 7: 8, 8: 9}
    all_ok &= check("257/sub  t2 histogram == landed claim",
                    sub257["t2_hist"] == claimed_257, str(sub257["t2_hist"]))
    all_ok &= check("257/sub  spectral gap: no t2 in {4,5,6}",
                    not any(t in sub257["t2_hist"] for t in (4, 5, 6)))
    all_ok &= check("257/sub  sum_phi t2 == C(16,2)*256 = 30720",
                    sub257["sum_t2"] == 120 * 256, str(sub257["sum_t2"]))
    pred257 = {(1, 0, (q2 - c) % q2) for c in H257} | {(0, 1, 0)}
    got257 = {phi for (phi, A, t2) in sub257["spikes"]}
    all_ok &= check("257/sub  spike set == predicted normalizer family (17)",
                    got257 == pred257)
    H257_2 = {(h * h) % q2 for h in H257}
    s257 = {phi: t2 for (phi, A, t2) in sub257["spikes"]}
    fp_ok257 = all(
        s257.get((1, 0, (q2 - c) % q2)) == (7 if c in H257_2 else 8) for c in H257
    ) and s257.get((0, 1, 0)) == 8 and (q2 - 1) in set(H257)
    all_ok &= check("257/sub  fixed-point law + (0,1,0)=8 + -1 in H", fp_ok257)

    out = {
        "q113_sub_t2_hist": sub["t2_hist"],
        "q113_rand1_t2_hist": rnd["t2_hist"],
        "q113_sub_spikes": [(list(p), a, t) for p, a, t in sub["spikes"]],
        "q257_sub_t2_hist": sub257["t2_hist"],
        "q257_sub_spikes": [(list(p), a, t) for p, a, t in sub257["spikes"]],
        "all_ok": bool(all_ok),
    }
    with open("/home/nubs/Git/ArkLib-moments/scripts/probes/moments/audit/reverify_census_out.json", "w") as f:
        json.dump(out, f, indent=1)
    print("ALL_OK" if all_ok else "DISCREPANCIES FOUND")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())

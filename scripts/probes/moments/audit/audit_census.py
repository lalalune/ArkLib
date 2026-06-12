#!/usr/bin/env python3
"""ADVERSARIAL AUDIT census recomputation (O133) — definition-direct, O(q^2 * n^2).

For each dual point phi=[f0:f1:f2] of PG(2,q) (reps (1,b,c) | (0,1,c) | (0,0,1)):
  A  = #{x in D : (f0,f1,f2) proportional to (1,x,x^2)}   (the universal points)
  t2 = #{ {x,y} in D, x != y, x,y NOT universal, f0*x*y - f1*(x+y) + f2 == 0 }
  s  = n - A
computed by a literal double loop over unordered pairs — no involution formula,
no partner map, no fiber argument. Independent asserts:
  * the satisfied pairs among non-universal points form a partial matching
    (each point appears in at most one counted pair);
  * sum over phi of t2 == C(n,2)*(q-1);
  * #\{phi with A=1\} == n.
Usage: audit_census.py q x1,x2,... [spike_threshold]
Prints JSON: {"t2_hist": {...}, "high": [[phi,A,s,t2], ...] (t2 >= thr), "sum_t2": int}
"""
import json
import sys
from itertools import combinations


def pg2(q):
    for b in range(q):
        for c in range(q):
            yield (1, b, c)
    for c in range(q):
        yield (0, 1, c)
    yield (0, 0, 1)


def main():
    q = int(sys.argv[1])
    D = sorted(int(t) % q for t in sys.argv[2].split(","))
    thr = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    n = len(D)
    assert all(D) and len(set(D)) == n

    pairs = list(combinations(D, 2))
    hist = {}
    high = []
    sum_t2 = 0
    a_count = 0
    for phi in pg2(q):
        f0, f1, f2 = phi
        universal = [x for x in D
                     if (f0 * 1) % q == 0 or True]  # placeholder, replaced below
        # proportionality (f0,f1,f2) ~ (1,x,x^2): requires f0 != 0 and then
        # f1 == f0*x, f2 == f0*x^2 (mod q). With canonical f0 in {0,1}: f0==1.
        universal = [x for x in D if f0 == 1 and f1 % q == x and f2 % q == (x * x) % q]
        A = len(universal)
        assert A <= 1
        a_count += A
        uset = set(universal)
        touched = {}
        t2 = 0
        for (x, y) in pairs:
            if x in uset or y in uset:
                continue
            if (f0 * x * y - f1 * (x + y) + f2) % q == 0:
                t2 += 1
                touched[x] = touched.get(x, 0) + 1
                touched[y] = touched.get(y, 0) + 1
        assert all(v == 1 for v in touched.values()), \
            f"NOT a partial matching at phi={phi}: {touched}"
        sum_t2 += t2
        hist[t2] = hist.get(t2, 0) + 1
        if t2 >= thr:
            high.append([list(phi), A, n - A, t2])

    assert a_count == n, f"#A-points {a_count} != n {n}"
    assert sum_t2 == (n * (n - 1) // 2) * (q - 1), \
        f"sum_t2 {sum_t2} != C(n,2)(q-1) {(n*(n-1)//2)*(q-1)}"
    assert sum(hist.values()) == q * q + q + 1
    high.sort(key=lambda r: (-r[3], r[0]))
    print(json.dumps({"t2_hist": {str(k): hist[k] for k in sorted(hist)},
                      "high": high, "sum_t2": sum_t2}, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())

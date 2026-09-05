#!/usr/bin/env python3
"""Dense, exact mu16 controls for the two-deletion collision obstruction.

Rebuild the actual polynomial pairs by interpolation and exact division.
Small-field collisions refute characteristic-independent injectivity only.
Even the control over the production prime uses 16, not 2**30, nodes.
"""

from collections import defaultdict
import json

from astra_mca_moment_rigidity_check import P, evaluate, mul, root, subtract
from astra_mca_paircover_four_cosets import label


def scale(f, a, p):
    return subtract(tuple(a * c % p for c in f), (0,), p)


def add(f, g, p):
    return subtract(f, scale(g, -1, p), p)


def divide_root(f, x, p):
    if f == (0,):
        return f
    q = [0] * (len(f) - 1)
    carry = f[-1]
    for j in range(len(f) - 2, -1, -1):
        q[j] = carry
        carry = (f[j] + x * carry) % p
    assert carry == 0
    q = subtract(tuple(q), (0,), p)
    assert subtract(mul(q, (-x % p, 1), p), f, p) == (0,)
    return q


def interpolate(nodes, values, p):
    result = (0,)
    for x, value in zip(nodes, values):
        f, denominator = (1,), 1
        for y in nodes:
            if x != y:
                f = mul(f, (-y % p, 1), p)
                denominator = denominator * (x - y) % p
        result = add(result, scale(f, value * pow(denominator, -1, p), p), p)
    assert all(evaluate(result, x, p) == y for x, y in zip(nodes, values))
    return result


def direction(row, p):
    a, b = row
    assert a or b
    return (1, b * pow(a, -1, p) % p) if a else (0, 1)


def check(p):
    n, m, cap = 16, 4, 7
    g = root(n, p)
    nodes = [pow(g, e, p) for e in range(n)]
    assert len(set(nodes)) == n
    i = pow(g, m, p)
    t = (0, 0, 0, 0, 1)
    q = add(t, (i,), p)
    residual = [e for e in range(n) if e % 4 == 3]
    values = (i, i * pow(2, -1, p) % p, 0)
    h = interpolate([nodes[e] for e in residual],
                    [values[label(e, n)] for e in residual], p)
    j = pow((1 - i) % p, -1, p)
    p0 = scale(subtract(t, (i,), p), j, p)
    q0 = scale(subtract((1,), t, p), j, p)
    old_first = (
        (0,),
        mul(subtract(t, (1,), p), add(p0, scale(h, 1 + i, p), p), p),
        scale(mul(subtract(t, (i,), p), subtract(q0, scale(h, 2, p), p), p), -1, p),
    )
    old_second = (
        (0,),
        scale(mul(subtract(t, (1,), p), q, p), 1 + i, p),
        scale(mul(subtract(t, (i,), p), q, p), 2, p),
    )
    a = evaluate(h, 1, p) * pow(evaluate(q, 1, p), -1, p) % p
    b = evaluate(h, g, p) * pow(evaluate(q, g, p), -1, p) % p
    assert a != b
    first = tuple(divide_root(subtract(f, scale(k, b, p), p), g, p)
                  for f, k in zip(old_first, old_second))
    second = tuple(divide_root(subtract(f, scale(k, a, p), p), 1, p)
                   for f, k in zip(old_first, old_second))
    assert all(len(f) - 1 <= cap for f in first + second)
    regions = [{e for e in range(n) if label(e, n) == owner} - {0, 1}
               for owner in range(3)]
    aa, bb, ss = regions
    assert list(map(len, regions)) == [4, 4, 6]
    cores = [aa | bb | {0, 1}, aa | ss, bb | ss]
    assert all(len(core) == 10 for core in cores)
    # Independently check the exact locator determinant, including its degree.
    det = subtract(mul(first[1], second[2], p), mul(second[1], first[2], p), p)
    loc = (1,)
    for e in sorted(aa | bb | ss):
        loc = mul(loc, (-nodes[e] % p, 1), p)
    assert len(det) - 1 == 14 and det == scale(loc, det[-1], p)
    received = []
    for e, x in enumerate(nodes):
        rows = [(evaluate(first[owner], x, p), evaluate(second[owner], x, p))
                for owner in range(3) if e in cores[owner]]
        assert rows and all(row == rows[0] for row in rows)
        received.append(rows[0])
    slots, classes = [], defaultdict(list)
    for owner, core in enumerate(cores):
        for e in sorted(set(range(n)) - core):
            row = ((received[e][0] - evaluate(first[owner], nodes[e], p)) % p,
                   (received[e][1] - evaluate(second[owner], nodes[e], p)) % p)
            key = direction(row, p)
            slot = {"owner": owner, "index": e, "row": row}
            slots.append(slot)
            classes[key].append(slot)
    assert len(slots) == 18
    result = {"prime": p, "n": n, "primitive_root": g, "degree_cap": cap,
              "core_sizes": list(map(len, cores)), "nonzero_slots": len(slots),
              "distinct_projective_directions": len(classes),
              "collision_classes": [v for v in classes.values() if len(v) > 1],
              "production_domain_checked": False}
    if p == 97:
        x = next(slot for slot in slots if slot["index"] == 4)
        y = next(slot for slot in slots if slot["index"] == 10)
        assert x["row"] != (0, 0) and y["row"] != (0, 0)
        assert (x["row"][0] * y["row"][1] - x["row"][1] * y["row"][0]) % p == 0
        result["explicit_collision"] = [x, y]
        result["first_polynomials"] = first
        result["second_polynomials"] = second
    return result


def main():
    fields = (17, 97, 113, 193, 241, P)
    results = [check(p) for p in fields]
    assert [r["distinct_projective_directions"] for r in results] == [13, 17, 17, 18, 17, 18]
    print(json.dumps({"status": "PASS_EXACT_DENSE_FINITE_CONTROLS",
                      "controls": results,
                      "characteristic_independent_injectivity_refuted": True,
                      "production_injectivity_proved": False,
                      "target_prize_proved": False}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

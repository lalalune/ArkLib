#!/usr/bin/env python3
"""Given (s, r, O, m), independently re-derive the B-completion (forced
fibers + first-k free axes rule) in pure Python and check raw antipodal
balance of the full multiset. Prints CERTIFIED + the full (O, m, B) on
success. Usage: recheck_om.py s m o1 o2 ... or with O as comma list.
"""
import sys

def main():
    s = int(sys.argv[1]); m = int(sys.argv[2])
    O = [int(x) for x in sys.argv[3:]]
    r = len(O)
    n, A, b = 2 * s, s // 2, (s + 1 - r) // 2
    assert len(set(O)) == r, "fibers not distinct"
    a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
    cnt = [0] * n
    for i in range(r):
        for j in range(i + 1, r):
            cnt[(a[i] + a[j]) % n] += 1
    for o in O:
        cnt[(2 * o) % n] += 1
    cnt[(3 * s // 2) % n] += 1
    # odd self-balance
    for t in range(1, s, 2):
        assert cnt[t] == cnt[t + s], f"odd imbalance at {t}"
    inO = set(O)
    forced, freeax, D = [], [], 0
    for c in range(A):
        d = cnt[2 * c] - cnt[2 * c + s]
        assert abs(d) <= 1, f"axis {c} overloaded d={d}"
        D += abs(d)
        if d == -1:
            assert c not in inO, f"blocked at {c}"
            forced.append(c)
        elif d == 1:
            assert (c + A) not in inO, f"blocked at {c+A}"
            forced.append(c + A)
        else:
            if c not in inO and (c + A) not in inO:
                freeax.append(c)
    h = D
    assert h <= b and (b - h) % 2 == 0, f"budget h={h} b={b}"
    k = (b - h) // 2
    assert k <= len(freeax), "free-axis capacity"
    B = forced + [f for c in freeax[:k] for f in (c, c + A)]
    assert len(B) == b and len(set(B)) == b and not (set(B) & inO)
    for f in B:
        cnt[(2 * f) % n] += 1
    for t in range(s):
        assert cnt[t] == cnt[t + s], f"final imbalance at {t}"
    print(f"CERTIFIED s={s} r={r} h={h} b={b} O={O} m={m}")
    print(f"B={sorted(B)}")

main()

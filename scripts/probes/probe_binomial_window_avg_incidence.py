import math

def fp_subgroup(p, n):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        order = 1
        y = cand % p
        while y != 1:
            y = (y * cand) % p
            order += 1
            if order > p:
                break
        if order == p - 1:
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x * h) % p
    return sorted(S)

def test(p, n):
    S = fp_subgroup(p, n)
    assert len(S) == n
    out = []
    for d in range(1, n):
        total = 0
        worst = 0
        for c in S:
            inc = sum(1 for x in S if pow(x, d, p) == c)
            worst = max(worst, inc)
            total += inc
        out.append((d, total, worst, math.gcd(d, n)))
    return out

cases = [(17,4),(41,4),(521,4),(73,8),(89,4),(97,8),(193,8),(337,8),(257,4),(257,8),(257,16),(4129,8)]
allpass = True
for p, n in cases:
    if (p - 1) % n != 0 or (p - 1) // n < 2:
        continue
    for d, total, worst, g in test(p, n):
        ok = (total == n) and (worst <= g)
        if not ok:
            allpass = False
        flag = "" if ok else "  <<< FAIL"
        print(f"p={p:5d} n={n:3d} d={d:3d}: sum_c inc={total:4d} (==n? {total==n})  worst_c={worst} gcd(d,n)={g}{flag}")
    print()
print("ALL PASS (window total == n, worst <= gcd):", allpass)

# Pin the exact decide-feasible witness: mu_8 in F_17, E_3 > 15*8^3.
from collections import Counter
from sympy import primitive_root


def main():
    p, n = 17, 8
    g = primitive_root(p)
    step = (p - 1) // n
    base = pow(g, step, p)
    G = sorted({pow(base, k, p) for k in range(n)})
    print("p=%d n=%d primitive_root=%d base(order %d)=%d" % (p, n, g, n, base))
    print("mu_8 =", G, " |G|=", len(G))
    # is it negation-closed? does -1 (=16) in G?
    print("neg-closed:", all(((-x) % p) in G for x in G), " contains 16(=-1):", 16 in G)
    cnt = Counter()
    for a in G:
        for b in G:
            for c in G:
                cnt[(a + b + c) % p] += 1
    e3 = sum(v * v for v in cnt.values())
    print("E_3(mu_8) over F_17 =", e3)
    print("15 * n^3 =", 15 * n ** 3, " breach:", e3 > 15 * n ** 3)
    print("char-0 census 15n^3-45n^2+40n =", 15 * n**3 - 45 * n**2 + 40 * n)
    print("char-p excess =", e3 - (15 * n**3 - 45 * n**2 + 40 * n))
    # also report E_2 for the record (should match 3n^2-3n=168 unconditionally)
    cnt2 = Counter()
    for a in G:
        for b in G:
            cnt2[(a + b) % p] += 1
    e2 = sum(v * v for v in cnt2.values())
    print("E_2(mu_8) over F_17 =", e2, " 3n^2-3n =", 3 * n**2 - 3 * n,
          " (r=2 rung holds:", e2 <= 3 * n**2, ")")


if __name__ == "__main__":
    main()

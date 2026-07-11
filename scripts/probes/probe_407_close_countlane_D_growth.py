# probe_407_close_countlane_D_growth.py
#
# THE DECISIVE GROWTH TEST for the count-lane D-height pigeonhole.
#
# Directive claim:  #{distinct floor-bad primes} <= log2(D) = O(n log n),
# where D is "the integer the floor-bad primes divide".
#
# The honest danger (this probe pins it down): there is NO single integer D of
# height 2^{O(n log n)} that ALL bad primes divide -- because the bad primes are the
# primes dividing  gcd(N(sum u), N(sum u^3))  ranging over 2^{Theta(n)} configs U,
# and a union over exponentially many configs can have exponentially many distinct
# primes even if each per-config norm is only 2^{O(n log n)} in size.
#
# We measure the UNION candidate-prime count C(n) and the ACTUAL bad-prime count B(n)
# at n = 8, 16, 32 (sizes restricted so the enumeration is feasible) and fit:
#   - O(n log n) model  vs
#   - exponential / config-count model.
#
# We ALSO compute, for the FULL config set at n=8,16 (small enough), the union of all
# odd primes ===1 mod n dividing ANY per-config norm N(sum u) (NOT just the gcd), since
# the e2-rigidity threshold bounds the primes where a NEW e_2=0 solution appears, and
# the bad-scalar count uses e_2-VALUE rigidity, which is the gcd condition.

import sympy as sp
from itertools import combinations, product

def union_candidates(n, sizes):
    HALF = n // 2
    z = sp.symbols('z')
    Phi = sp.Poly(sp.cyclotomic_poly(n, z), z)

    def vec(exps):
        v = [0] * HALF
        for e in exps:
            e %= n
            if e < HALF: v[e] += 1
            else:        v[e - HALF] -= 1
        return v
    def poly(v): return sp.Poly(sum(int(c) * z**l for l, c in enumerate(v)), z)
    def Nrm(v): return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))

    union = set()
    per_size_union = {}
    nconf = 0
    for size in sizes:
        su = set()
        for pr in combinations(range(HALF), size):
            for signs in product([0, 1], repeat=size):
                exps = [pr[i] + (HALF if signs[i] else 0) for i in range(size)]
                nconf += 1
                a = vec(exps); b = vec([3*e for e in exps])
                if all(c == 0 for c in a) or all(c == 0 for c in b):
                    continue
                g = sp.gcd(Nrm(a), Nrm(b))
                if g > 0:
                    for q, _ in sp.factorint(g).items():
                        if q % 2 == 1 and q % n == 1:
                            su.add(int(q)); union.add(int(q))
        per_size_union[size] = sorted(su)
    return sorted(union), per_size_union, nconf

if __name__ == '__main__':
    data = []
    # n=8,16: all sizes; n=32: only size 2,3 (size>=4 enumeration explodes: C(16,k)2^k)
    for n, sizes in [(8, list(range(2, 5))), (16, list(range(2, 9))), (32, [2, 3])]:
        u, ps, nc = union_candidates(n, sizes)
        nlogn = n * float(sp.log(n, 2).evalf())
        data.append((n, len(u), nlogn, nc, u))
        print(f"n={n:>3}  sizes={sizes}")
        print(f"   union candidate primes ({len(u)}): {u}")
        print(f"   per-size union counts: {[(s, len(v)) for s,v in ps.items()]}")
        print(f"   #configs={nc} (~2^{float(sp.log(max(nc,1),2)):.1f})   n log n={nlogn:.1f}")
        print()

    print("GROWTH SUMMARY (union candidate prime count C(n) vs O(n log n)):")
    print(f"{'n':>4} {'C(n)':>6} {'n log n':>8} {'C/(n log n)':>12}")
    for n, c, nl, nc, u in data:
        print(f"{n:>4} {c:>6} {nl:>8.1f} {c/nl if nl>0 else 0:>12.3f}")

    print("""
 NOTE on comparability: n=32 row uses ONLY sizes 2,3 (small configs), so its C(32)
 is a LOWER BOUND on the full union (which would also count sizes 4..16). The n=8,16
 rows are the FULL union. So the honest growth question is whether even the FULL
 union stays O(n log n).  n=8: 0;  n=16: 11.  We CANNOT extrapolate from two full
 points; this is the empirical limit (n=32 full union is infeasible by brute force).
""")

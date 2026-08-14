# probe_407_close_countlane_D_singleresultant.py
#
# Sharpen the count-lane D-height question.  The directive's pigeonhole needs
#   #{distinct floor-bad primes}  <=  log2(D)  =  O(n log n).
#
# There are TWO candidate definitions of D, with VERY different heights:
#
#   (D_union) D = lcm/product over ALL configs U of the per-config obstruction
#             gcd(N(sum u), N(sum u^3)).  There are ~ 2^{Theta(n)} configs, so even if
#             each contributes a height-O(n log n) factor, the union has height
#             2^{Theta(n)} * O(n log n) and #primes can be 2^{Theta(n)} >> n log n.
#             ==> (D_union) does NOT give O(n log n) by a size bound.
#
#   (D_single) The e2_extra_solution_threshold of E2VanishRigidityModP is a PER-CONFIG
#             statement: each bad config forces p <= (n^2+n)^{n/2}.  Quantifying over
#             configs, the bad-prime SET is {p : EXISTS bad config at p}.  This is a
#             UNION over exp-config indexed by the SAME fold; the bound caps each prime's
#             SIZE at (n^2+n)^{n/2}, giving (H1) max bad prime <= 2^{O(n log n)} but NOT
#             (H2) #distinct bad primes <= O(n log n).
#
# This probe answers EXACTLY: for n=8,16, how many distinct candidate / actual bad
# primes are there, and what is log2 of the SINGLE-config max norm vs the union product?
# It directly tests whether the "log D" pigeonhole step is sound or a count/size confusion.

import sympy as sp
from itertools import combinations, product

def analyze(n, sizes=None):
    HALF = n // 2
    z = sp.symbols('z')
    Phi = sp.Poly(sp.cyclotomic_poly(n, z), z)
    if sizes is None:
        sizes = list(range(2, HALF + 1))

    def vec(exps):
        v = [0] * HALF
        for e in exps:
            e %= n
            if e < HALF: v[e] += 1
            else:        v[e - HALF] -= 1
        return v
    def poly(v): return sp.Poly(sum(int(c) * z**l for l, c in enumerate(v)), z)
    def Nrm(v): return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))

    def configs(size):
        out = []
        for pr in combinations(range(HALF), size):
            for signs in product([0, 1], repeat=size):
                out.append([pr[i] + (HALF if signs[i] else 0) for i in range(size)])
        return out

    # Collect, per config, the single norms N(sum u), N(sum u^3) and their gcd.
    per_config_logmax = 0.0       # max over configs of log2(max(N_a, N_b))  -- the SINGLE-config height
    union_primes = set()          # union over configs of odd primes ===1 mod n dividing gcd
    n_configs = 0
    n_nontrivial = 0
    for size in sizes:
        for exps in configs(size):
            n_configs += 1
            a = vec(exps); b = vec([3*e for e in exps])
            if all(c == 0 for c in a) or all(c == 0 for c in b):
                continue
            n_nontrivial += 1
            Na, Nb = Nrm(a), Nrm(b)
            mx = max(Na, Nb)
            if mx > 1:
                per_config_logmax = max(per_config_logmax, float(sp.log(mx, 2).evalf()))
            g = sp.gcd(Na, Nb)
            if g > 0:
                for pr, _ in sp.factorint(g).items():
                    if pr % 2 == 1 and pr % n == 1:
                        union_primes.add(int(pr))

    union_primes = sorted(union_primes)
    nlogn = n * float(sp.log(n, 2).evalf())
    print(f"\n=== n={n} ===")
    print(f"  #configs enumerated            = {n_configs}  (~2^{float(sp.log(max(n_configs,1),2)):.1f})")
    print(f"  #nontrivial (primitive) configs= {n_nontrivial}")
    print(f"  SINGLE-config height: max log2(N) over configs = {per_config_logmax:.2f}")
    print(f"    (e2 fold size bound predicts <= (n/2)*log2(n^2+n) = {HALF*float(sp.log(n*n+n,2)):.2f})")
    print(f"  UNION over configs: #distinct odd primes ===1 mod n dividing some gcd = {len(union_primes)}")
    print(f"  target O(n log n) = {nlogn:.1f}")
    print(f"  union primes: {union_primes}")
    return len(union_primes), per_config_logmax, nlogn, n_configs

if __name__ == '__main__':
    print("Testing whether #distinct candidate primes grows like O(n log n) (pigeonhole-safe)")
    print("or like the config count 2^Theta(n) (pigeonhole-BROKEN).")
    rows = []
    for n in [8, 16]:
        u, h, nl, nc = analyze(n)
        rows.append((n, u, h, nl, nc))
    print("\n SUMMARY")
    print(f"{'n':>4} {'#union primes':>14} {'1cfg log2N':>11} {'n log n':>8} {'#configs':>9}")
    for n, u, h, nl, nc in rows:
        print(f"{n:>4} {u:>14} {h:>11.1f} {nl:>8.1f} {nc:>9}")
    print("""
 INTERPRETATION:
  - If #union primes <= n log n with margin AND grows slowly (8 -> 16 ~ doubling),
    the count-lane D-height pigeonhole is plausible at the SIZE level.
  - The SINGLE-config height log2(N) is the e2-species bound (<= (n/2)log2(n^2+n)).
    The e2 fold machinery bounds THIS (per-config max prime), giving (H1) not (H2).
  - The DECISIVE question: is the UNION prime count O(n log n) or 2^{Theta(n)}?
    n=8->n=16 union count tells us the growth.
""")

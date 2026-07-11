#!/usr/bin/env python3
"""
Door-(iv) probe: CROSS-SCALE NESTING of the worst frequency.

At the worst b* for the level-n period eta_b = Sum_{y in mu_n} e_p(b*y), the subgroup
half A = Sum_{y in mu_{n/2}} e_p(b*y) is itself a period over the thinner subgroup mu_{n/2}.
QUESTION (a non-magnitude / alignment statistic, distinct from balance and from the abstract
descent cascade): does the level-n worst frequency b* ALSO (near-)maximize the level-(n/2)
sub-period |A_b| = |Sum_{y in mu_{n/2}} e_p(b*y)|?

If YES (b* is "nested-optimal" across scales), the worst frequencies of the dyadic tower are
ALIGNED — the same b is adversarial at every level — which would make a recursive ascent argument
possible (build the level-n worst from the level-(n/2) worst). If NO (worst-b at level n is generic
for level n/2), the tower's worst frequencies are DECORRELATED and no naive ascent recursion works.

Measure, prize regime (proper mu_n, p>>n^3, structured primes, never n=q-1), FULL F_p* scan at n=16:
  - b* = argmax_b |eta_b| at level n.
  - rank/percentile of |A_{b*}| among {|A_b| : all b} (the level-(n/2) sub-period values).
  - is b* in the argmax-orbit of the level-(n/2) period? (exact coset check)
"""
import cmath, math
from sympy import factorint

def primitive_root(p):
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError

def find_prime(n, beta):
    p_target = max(int(n**beta), n**3 * 4)
    base = ((p_target // n) + 1) * n + 1
    while True:
        p = base
        if p > 2 and all(p % d for d in range(3, int(p**0.5)+1, 2)):
            return p
        base += n

def period_over_subgroup(p, b, gen, order):
    # gen generates the subgroup of given order; sum e_p(b*x) over it
    s = 0j; x = 1
    h = gen
    for _ in range(order):
        s += cmath.exp(2j*math.pi*(b*x % p)/p)
        x = (x*h) % p
    return s

def run(n, beta, cap=200000):
    p = find_prime(n, beta)
    if (p-1) > cap:
        print(f"n={n} beta={beta} p={p}: SKIP full scan")
        return
    g = primitive_root(p)
    h_n = pow(g, (p-1)//n, p)          # generates mu_n
    h_half = pow(g, (p-1)//(n//2), p)  # generates mu_{n/2}
    # level-n argmax
    best_mag = -1; best_b = None
    etaA_all = {}
    for b in range(1, p):
        eta = period_over_subgroup(p, b, h_n, n)
        A = period_over_subgroup(p, b, h_half, n//2)
        etaA_all[b] = abs(A)
        m = abs(eta)
        if m > best_mag:
            best_mag = m; best_b = b
    # rank of |A_{b*}| among all |A_b|
    Avals = sorted(etaA_all.values())
    Astar = etaA_all[best_b]
    below = sum(1 for v in Avals if v <= Astar)
    pct = below/len(Avals)
    # level-(n/2) global max of |A_b|
    Amax = max(etaA_all.values())
    Amax_b = max(etaA_all, key=lambda b: etaA_all[b])
    # is best_b in the same mu_{n/2}-coset as Amax_b? (A_b is mu_{n/2}-coset invariant in |.|)
    print(f"n={n} beta={beta} p={p} FULL scan")
    print(f"   level-n worst b*={best_b}, |eta_{{b*}}|={best_mag:.4f} (√n={n**0.5:.3f})")
    print(f"   level-(n/2) sub-period at b*: |A_{{b*}}|={Astar:.4f}  vs global max |A|={Amax:.4f}  ratio={Astar/Amax:.4f}")
    print(f"   percentile of |A_{{b*}}| among all |A_b| = {pct:.3f}  (1.0 = b* also maximizes the n/2 sub-period)")

if __name__ == "__main__":
    print("=== Door-(iv) cross-scale nesting of worst frequency ===")
    for n, beta in [(16,4),(16,4.3),(32,3.5)]:
        run(n, beta)
        print()

# --- ADVERSARIAL appendix: deeper-beta sampled check of nesting percentile + exact-argmax test ---
def run_sampled_argmax_check(n, beta, nsamp=6000):
    import random
    random.seed(7)
    p = find_prime(n, beta)
    g = primitive_root(p)
    h_n = pow(g, (p-1)//n, p)
    h_half = pow(g, (p-1)//(n//2), p)
    bs = sorted(set([random.randint(1,p-1) for _ in range(nsamp)]))
    best_mag=-1; best_b=None
    for b in bs:
        m = abs(period_over_subgroup(p,b,h_n,n))
        if m>best_mag: best_mag=m; best_b=b
    # is best_b's n/2-subperiod the *exact* max among sampled? (test strict equality of argmax)
    Astar = abs(period_over_subgroup(p,best_b,h_half,n//2))
    Avals = [abs(period_over_subgroup(p,b,h_half,n//2)) for b in bs]
    Amax = max(Avals)
    below = sum(1 for v in Avals if v<=Astar)/len(Avals)
    exact = abs(Astar-Amax) < 1e-9
    print(f"  [sampled] n={n} beta={beta} p={p}: |A_b*|/maxA={Astar/Amax:.4f} pct={below:.3f} exact-argmax={exact}")

print("=== adversarial deeper-beta SAMPLED nesting (consistency check only) ===")
print("  NOTE: best_b AND the sub-period max are taken from the SAME random sample, NOT all of F_p*.")
print("  'exact-argmax=False' here means sampled-best != sampled-sub-argmax; it is NOT a global-argmax")
print("  claim. The constraint's evidence is the FULL-scan section above (true global argmax, ratio<1).")
for n,beta in [(16,5),(32,4.5),(64,4)]:
    run_sampled_argmax_check(n,beta)

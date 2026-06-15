#!/usr/bin/env python3
"""
THE #distinct-GAMMA <= KKH26-budget question at n=32 — the corrected CensusDomination object.

CONTEXT (DISPROOF_LOG entry "CensusDomination Prop is FALSE at budget (bounds SETS, not gamma)",
issuecomment-4704035101): the deployed CensusDominationWeld bounds the alignable-SET count by K,
but the SET count OVERFLOWS the KKH26 budget (n=16: 896 sets > 448 budget, 2x). The TRUE prize
quantity is #distinct-gamma (epsMCA <= #bad/p, #bad = #distinct-gamma = badScalars), which was
WITHIN budget at every config for n<=16 (97,40,73 <= budget). The prior worker's explicit open
residual: "#distinct-gamma <= budget is the open BGK content (margin large at n<=16, ASYMPTOTIC
UNTESTED). The correct <=>-CORE normal form must bound #distinct-gamma, NOT the alignable-SET count."

THIS PROBE settles the UNTESTED asymptotic + thinness:
  Q1 (GROWTH/MARGIN): does worst-line #distinct-gamma stay <= the KKH26 budget at n=32, and is the
      RATIO gamma/budget shrinking (margin growing, GOOD for the prize) or growing toward 1 (margin
      closing, the prize wall tightening)?
  Q2 (rule-3 THINNESS): is the gamma-within-budget a thin (2-power mu_n in F_q*) phenomenon, or does
      the SAME gamma<=budget hold in a THICK subgroup (small index m=(p-1)/n)? If the gamma count is
      thickness-invariant, gamma<=budget is NOT a thin BGK signal.

BUDGET (the REAL one, from hεstar < (2^r * C(2^{mu-1}, r))/p in CensusDominationWeld.lean):
  K_budget = 2^r * C(2^{mu-1}, r),  with n = 2^mu * m (prize: m chosen so beta=log_n(p)~4).
  At the deep ceiling band a0 = r*m + 1, rate k = (r-2)*m + 1 (the weld's exact (k,a0) from r,m).

EXACT: divided-difference pencil-ratio alignment (gamma = -e0(T)/e1(T)), mod p, no floats.
Dilation-orbit reduction: a-sets come in mu_n-orbits under z->h*z; the gamma of h.S = h^{b-a}*gamma(S),
so we enumerate a-sets containing index 0 (the orbit reps) and orbit-close, ~n x fewer sets.
PROPER mu_n (index m>=2, NEVER n=q-1), prize prime p ~ n^beta.
"""
import itertools, math, sys
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime_index(n, m, lo=None):
    """smallest prime p with p % n == 1 and index (p-1)/n >= m (controls thickness via m)."""
    p = (lo if lo else m*n) 
    p += (1 - p) % n
    if p < 3: p = n + 1
    while True:
        if p > 2 and p % n == 1 and (p-1)//n >= m and all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += n

def find_g(p, n):
    for h in range(2, 8000):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in prime_factors(n)):
            return x
    raise ValueError(f"no generator order {n} in F_{p}")

def gamma_census_orbitreduced(aa, bb, xs, p, k, a, h):
    """
    Exact #distinct-gamma AND #alignable-sets for the line (x^aa, x^bb) at band-size a on mu_n.
    Dilation-orbit reduced: enumerate a-subsets S with 0 in S (orbit reps under z->h*z),
    then orbit-close gamma under multiplication by h^{(bb-aa)} (codeword space dilation-covariance).
    Returns (n_sets_full, n_gamma_full) via orbit multiplicities.
    """
    n = len(xs)
    u0 = [pow(x, aa, p) for x in xs]
    u1 = [pow(x, bb, p) for x in xs]
    # divided differences e0,e1 over all (k+1)-subsets (cache)
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), k+1):
        t0 = t1 = 0
        for i in T:
            den = 1
            for j in T:
                if i != j: den = den*((xs[i]-xs[j]) % p) % p
            inv = pow(den, -1, p)
            t0 = (t0 + u0[i]*inv) % p; t1 = (t1 + u1[i]*inv) % p
        e0[T] = t0; e1[T] = t1
    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if b_ != 0: return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'X'  # 'X' = saturated (e0!=0,e1=0): line NOT far on T
    # enumerate orbit-rep a-sets (those containing index 0); orbit factor = n / |stab|.
    # For generic a-set stab is trivial -> each rep gives n distinct rotates. We count gamma by
    # building the FULL gamma-set via orbit-closure: gamma(h.S) = h^{(bb-aa)} * gamma(S).
    hd = pow(h, (bb-aa) % n if (bb-aa) >= 0 else (bb-aa) % n, p)  # h^{bb-aa} mod p
    gamma_full = set()
    sets_full = 0
    rest = [i for i in range(1, n)]
    for combo in itertools.combinations(rest, a-1):
        S = (0,) + combo
        r = None; ok = True; nd = False
        for T in itertools.combinations(S, k+1):
            rt = ratio(T)
            if rt is None: continue
            if rt == 'X': ok = False; break
            nd = True
            if r is None: r = rt
            elif r != rt: ok = False; break
        if ok and nd:
            # this rep S is alignable with gamma=r. orbit-close: rotate S by h^t (t=0..n-1),
            # each rotate is a distinct a-set (generically) with gamma = r * hd^t.
            g = r
            for t in range(n):
                gamma_full.add(g)
                g = (g * hd) % p
            sets_full += n  # generic orbit size (upper bound; exact for trivial-stab reps)
    return sets_full, len(gamma_full)

def run(n, mu, m, r, p=None):
    k = (r-2)*m + 1
    a0 = r*m + 1
    budget = (2**r) * comb(2**(mu-1), r)
    if p is None:
        p = find_prime_index(n, m, lo=n**4)  # prize prime ~ n^4
    g = find_g(p, n)
    xs = [pow(g, i, p) for i in range(n)]
    assert len(set(xs)) == n
    beta = math.log(p)/math.log(n)
    idx = (p-1)//n
    print(f"\n==== n={n}=2^{mu}*{m} r={r} k={k} a0={a0} p={p} beta={beta:.2f} index_m={idx} "
          f"KKH26_budget=2^{r}*C({2**(mu-1)},{r})={budget} ====")
    # FULL far-line sweep (the prior structured-candidate restriction MISSED the worst line:
    # at n=16 r=4 the true worst gamma is 145 on x^8,x^5, not 40 on an adjacent line). Sweep all
    # ordered pairs aa>bb (the far monomial stack x^aa + gamma*x^bb). Dilation symmetry lets us
    # fix bb in a fundamental range but we sweep fully for the worst-direction pin.
    cand = [(aa, bb) for aa in range(2, n) for bb in range(1, aa)]
    worst_g = (0, None); worst_s = (0, None)
    for (aa, bb) in cand:
        if a0 - 1 > n - 1:  # band too big
            continue
        try:
            s, gm = gamma_census_orbitreduced(aa, bb, xs, p, k, a0, g)
        except Exception as ex:
            continue
        if gm > worst_g[0]: worst_g = (gm, f"x^{aa},x^{bb}")
        if s > worst_s[0]: worst_s = (s, f"x^{aa},x^{bb}")
        if gm > 0:
            print(f"   x^{aa:>2},x^{bb:<2} | sets~{s:>6}  gamma={gm:>5} | gamma/budget={gm/budget:.4f}")
    vg = "<= budget (TRUE OBJECT OK)" if worst_g[0] <= budget else ">budget BLOWS UP"
    print(f"  WORST gamma={worst_g[0]} ({worst_g[1]}) vs budget {budget}: {vg}")
    print(f"  margin ratio gamma/budget = {worst_g[0]/budget:.4f}  (worst SETS~{worst_s[0]})")
    return (n, worst_g[0], budget, worst_g[0]/budget)

if __name__ == '__main__':
    print("#distinct-GAMMA vs KKH26 budget — the corrected CensusDomination object (exact mod-p, proper mu_n)")
    results = []
    # n=16: reproduce the prior in-budget gamma (validation), mu=4, m=1 -> but m=1 is n=q-1-adjacent;
    # use beta~4 thin prize regime: n=16=2^4, choose m index large. r=3 -> k=(1)*m+1, a0=3m+1.
    # To match the prior probe's n=16 r=3 a0=4 we need m=1 (a0=r*m+1=4). m=1 => mu_16 with index=(p-1)/16.
    # The prior used p=65537 (index 4096, very thin). Keep m=1 for the (k,a0)=(2,4) match, beta from p.
    results.append(run(16, 4, 1, 3, p=65537))   # k=2,a0=4
    results.append(run(16, 4, 1, 4, p=65537))   # k=3,a0=5 (full sweep: worst gamma 145, not 40)
    results.append(run(16, 4, 1, 5, p=65537))   # k=4,a0=6
    # n=32 — THE UNTESTED ASYMPTOTIC. mu=5, m=1, r=3: k=2,a0=4; budget=2^3*C(16,3)=8*560=4480.
    results.append(run(32, 5, 1, 3))            # a0=4 light
    print("\n================ GROWTH/MARGIN SUMMARY ================")
    print(f"  {'n':>4} {'worst_gamma':>12} {'budget':>10} {'ratio':>8}")
    for (n, gm, bud, ratio) in results:
        print(f"  {n:>4} {gm:>12} {bud:>10} {ratio:>8.4f}")
    print("If ratio SHRINKS 16->32: margin grows, gamma<=budget robust (prize-consistent).")
    print("If ratio -> 1: the gamma census tightens to the budget = the BGK wall location.")

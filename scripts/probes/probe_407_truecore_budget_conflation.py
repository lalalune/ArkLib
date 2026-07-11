#!/usr/bin/env python3
"""
probe_407_truecore_budget_conflation.py  (#444 -- CORRECTION of the "first floor-consistent signal on
                                          the canonical #bad object" claim: TWO independent artifacts)

CONTEXT. A recent grind report + DISPROOF_LOG entry (probe_407_truecore_B_growth.py, brick ed1db3379)
reported that on the CANONICAL OpenCoreConditionalPin object #bad, the shallowest-band (k=1, a=3) ratio
    ratio(n) = #bad / budget,   budget = 2^r * C(2^{mu-1}, r)   [= 4*C(n/2,2) at r=2]
is BOUNDED BELOW 1 (~0.26), labeled "FLOOR-consistent" and "the FIRST canonical-#bad face that does
NOT march to Johnson." We show this read rests on TWO independent artifacts; corrected, the shallow-band
incidence is super-linear and gives NO evidence of a window-radius delta* floor.

THE CANONICAL OBJECT (OpenCoreConditionalPin.lean, exact):
  WorstCaseIncidenceBounded C delta B :  I(delta) = #{gamma : x^a+gamma*x^b is delta-close to RS[k]} <= B
  with the GOVERNING-LAW budget  B = floor(q*eps*) ~ n   (eps*=2^-128, q~n*2^128). I(delta) counts
  distinct gamma where the affine line is delta-close = a deg-<=k codeword AGREES on >= ceil((1-delta)n)
  domain points. At the shallowest band k=1, a=3: a deg-<=1 (affine) codeword agrees at >=3 points,
  i.e. >=3 of the points (x_i, u0(x_i)+gamma*u1(x_i)) are COLLINEAR.

ARTIFACT 1 -- BUDGET CONFLATION (census ~n^2/2, sum 3^{n/2}, vs canonical q*eps*~n):
  The "budget" 2^r*C(2^{mu-1},r) is the per-band CENSUS / stack-enumeration budget. At r=2 it is
  4*C(n/2,2) ~ n^2/2, and SUMMED over all bands  sum_r 2^r*C(2^{mu-1},r) = (1+2)^{n/2} = 3^{n/2}
  (EXPONENTIAL in n, e.g. 3^32 ~ 1.85e15 at n=64) -- NOT a decomposition of q*eps* ~ n. A method
  "feasible within the 3^{n/2} census budget" is VACUOUS w.r.t. the prize budget ~n. Normalizing a
  Theta(n^2) count by a Theta(n^2) per-band census budget yields a flat ~0.26 BY CONSTRUCTION; it is
  not a sub-(q*eps*) floor.

ARTIFACT 2 -- THE PUBLISHED ENGINE UNDERCOUNTS (drops collinear-but-NOROOT subsets):
  probe_407_truecore_B_growth.py counts a 3-subset only if ALL THREE pairwise 1st-divided-difference
  ratios coincide AND none is a 'NOROOT' (e1=0, e0!=0) pair -- a 'NOROOT' pair aborts the WHOLE subset.
  But three points can be COLLINEAR (a genuine deg-<=1 agreement => a real bad gamma) even when one
  pair is vertical/NOROOT. The collinearity-determinant engine (correct object) is a strict SUPERSET:
  at n=8 line(4,2) the published engine gives 5, the correct engine gives 17 (the 5 are a subset of
  the 17; 12 valid gamma are dropped). So the published #bad (5,25,113,481) UNDERCOUNTS the true I.

CORRECTED MEASUREMENT (collinearity engine = the true >=3-agreement object; exact mod-p, PROPER mu_n
m=(p-1)/n>1, p~n^4..n^4.3, p==1 mod n, NEVER n=q-1, multi-prime, worst over a far-line family):
    n :        8     16      32       64
  #bad(corr): 17    232    2320    ~20224       (#bad/n: 2.1, 14.5, 72.5, 316 -- super-linear)
  (fixed line (4,2) is p-INDEPENDENT; the worst-OVER-lines value has mild p-jitter at n=64.)
  #bad(published,undercount): 5  25  113  481   (= n^2/8 - n/2 + 1 exactly, p-indep -- still Theta(n^2))

VERDICT (rule-4 mapped correction; rule-6 honest, NOT a closure):
  Against the CANONICAL eps* budget B ~ n, the shallowest-band incidence is super-linear (Theta(n^2)
  even by the undercount; faster by the correct engine) = SUPER-budget and GROWING = Johnson-side, not
  floor. The "0.26 floor-consistent canonical signal" is the JOINT product of (1) a census-vs-eps*
  budget conflation and (2) an undercounting engine -- both push the true picture MORE Johnson-side.
  SEPARATE honest caveat: a=3 reads incidence at near-trivial agreement (delta ~ 1, OUTSIDE the prize
  window (1-sqrt(rho), 1-rho-Theta(1/log n))), so this super-budget growth does NOT by itself refute
  the WINDOW-RADIUS floor -- it is the wrong delta AND the wrong budget to read floor-vs-Johnson on.
  Net: removes a budget-conflated + undercounted "floor" read; the canonical window-radius
  WorstCaseIncidenceBounded at B~n remains OPEN and UNMEASURED at the prize delta*. CORE not closed.
"""
import itertools, math


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while not is_prime(p): p += n
    return p


def find_g(p, n):
    m = (p - 1) // n
    assert m > 1, "PROPER subgroup only (m>1); never n=q-1"
    for h in range(2, 20000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError


def nbad_published(A, B, xs, p):
    """The PUBLISHED engine (probe_407_truecore_B_growth.py): all-pairwise-ratios-coincide + NOROOT abort.
    Reproduced to expose its undercount."""
    n = len(xs)
    u0 = [pow(x, A, p) for x in xs]; u1 = [pow(x, B, p) for x in xs]
    e0 = {}; e1 = {}
    for (i, j) in itertools.combinations(range(n), 2):
        di = pow((xs[i] - xs[j]) % p, -1, p)
        e0[(i, j)] = (u0[i] - u0[j]) * di % p
        e1[(i, j)] = (u1[i] - u1[j]) * di % p
    def ratio(t):
        a_, b_ = e0[t], e1[t]
        if b_ != 0: return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'
    pinned = set()
    for S in itertools.combinations(range(n), 3):
        r = None; ok = True; nd = False
        for t in itertools.combinations(S, 2):
            rt = ratio(t)
            if rt is None: continue
            if rt == 'NOROOT': ok = False; break
            nd = True
            if r is None: r = rt
            elif r != rt: ok = False; break
        if ok and nd: pinned.add(r)
    return len(pinned)


def nbad_correct(A, B, xs, p):
    """CORRECT object: #distinct gamma s.t. SOME 3-subset is collinear in (x, u0+gamma*u1) =
    a deg-<=1 codeword agrees on >=3 points. Collinearity det is LINEAR in gamma => <=1 gamma per subset."""
    n = len(xs)
    u0 = [pow(x, A, p) for x in xs]; u1 = [pow(x, B, p) for x in xs]
    pinned = set()
    for (i, j, l) in itertools.combinations(range(n), 3):
        dxj = (xs[j] - xs[i]) % p; dxl = (xs[l] - xs[i]) % p
        a0 = (u0[j] - u0[i]) % p; a1 = (u1[j] - u1[i]) % p
        b0 = (u0[l] - u0[i]) % p; b1 = (u1[l] - u1[i]) % p
        c = (dxj * b0 - dxl * a0) % p
        d = (dxj * b1 - dxl * a1) % p
        if d != 0:
            pinned.add((-c) * pow(d, -1, p) % p)
        # d==0: gamma-free collinearity (degenerate / all-gamma) -- excluded (rule-2 coset-pencil trap).
    return len(pinned)


def worst(fn, n, p):
    g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
    lines = [(4, 2), (6, 4), (8, 4), (n // 2 + 1, n // 2 - 1),
             (n - 1, n - 3), (n // 2, n // 4), (6, 2), (8, 6)]
    best = 0
    for (A, B) in lines:
        if A >= n or A == B: continue
        c = fn(A, B, xs, p)
        if c > best: best = c
    return best


def main():
    print("ARTIFACT 2 -- undercount, fixed worst line (4,2), n=8: published vs correct engine")
    n = 8; p = next_prime_cong1(n, int(n ** 4)); g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
    print(f"  published={nbad_published(4, 2, xs, p)}  correct={nbad_correct(4, 2, xs, p)} "
          f"(published is a strict subset)")
    print()
    print("ARTIFACT 1 -- census/per-band budget 2^r*C(2^{mu-1},r) sums to 3^{n/2} (exponential), NOT q*eps*~n:")
    for mu in (3, 4, 5, 6):
        n = 2 ** mu; h = 2 ** (mu - 1)
        print(f"  n={n:3d}: per-band(r=2)={4*math.comb(h,2):6d}~n^2/2 ; sum_r=3^(n/2)={3**h} ; q*eps*~n={n}")
    print()
    print("CORRECTED #bad vs BOTH budgets (census ~n^2/2 and canonical B~n), multi-prime:")
    print(f"{'n':>4} {'#bad_pub':>9} {'#bad_corr':>10} {'/census':>9} {'/B~n':>8}  p-indep(corr)")
    for mu in (3, 4, 5, 6):
        n = 2 ** mu
        pub = []
        cor = []
        for lo in (int(n ** 4.0), int(n ** 4.3)):
            p = next_prime_cong1(n, lo)
            pub.append(worst(nbad_published, n, p))
            cor.append(worst(nbad_correct, n, p))
        census = 4 * math.comb(n // 2, 2)
        pind = len(set(cor)) == 1
        print(f"{n:>4} {pub[0]:>9} {cor[0]:>10} {cor[0]/census:>9.3f} {cor[0]/n:>8.2f}  "
              f"p-indep={pind} (pub={pub}, corr={cor})", flush=True)
    print()
    print("=> Both artifacts push Johnson-side. The shallow-band 'floor-consistent canonical signal'")
    print("   is unsupported. Canonical window-radius WorstCaseIncidenceBounded at B~n remains OPEN.")


if __name__ == "__main__":
    main()

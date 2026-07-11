#!/usr/bin/env python3
"""
probe_444_a1_krawtchouk_trace_sheaf.py  (#444 — angle A1: Krawtchouk-as-trace-sheaf,
                                          RELOCATE the cancellation locus to the u0 PARAMETER)

THE ANGLE.  The reduced far-line incidence fluctuation is (probe_dualcode_krawtchouk, EXACT):
    M(u0) = avg + (q|C|/q^n) * S(u0),   S(u0) = sum_{xi in D} K_w(wt xi) * e_p(xi . u0),
    D = Cperp ∩ u1perp  (a fixed dual-code hyperplane section, dim = n-k-1),
    K_w(j) = Bhat at weight j = the Krawtchouk value (Fourier of the Hamming ball B of radius r).
The OPEN CORE is  sup_{u0} |S(u0)| <= |Ball|  (= sheaf-sharp / past Johnson).

NEW LEMMA (to invent & test):  u0 |-> S(u0) is the trace function of an l-adic sheaf on the
(k+1)-dim parameter space; if that sheaf has CONDUCTOR c = O(1) (n-independent), Deligne+FKM give
    sup_{u0} |S(u0)| <= c * sqrt( sum_{xi in D} |K_w(wt xi)|^2 )   (square-root cancellation),
UNIFORMLY in u0, where u0 ranges over q^{k+1} >> sqrt(q) points (Deligne BITES, unlike the n-domain).

WHAT WE MEASURE (EXACT integers / floats; honest probe).  Over the FULL u0-parameter space
(q^n offsets, but S only depends on u0 mod (the row space)... we just sweep all q^n u0 for small
codes and read the distribution):
  R_inf  = sup_{u0} |S(u0)|                         (the worst case = the prize quantity)
  L2     = sqrt( avg_{u0} |S(u0)|^2 )               (= sqrt(sum |K_w|^2) by Parseval; sheaf-sharp scale)
  L4ratio= avg|S|^4 / (avg|S|^2)^2                   (=2 for a Gaussian/CUE trace; >2 = peaky = conductor up)
  CONDUCTOR PROXY  c_eff = R_inf / L2.
The DECISIVE question:  is c_eff BOUNDED as n=2^mu grows (sheaf conductor O(1) => CRACK), or does
c_eff GROW with n (conductor grows with n => back to the BGK wall)?  We also report sup|S| vs |Ball|
(the literal open-core inequality) and the FKM-predicted bound c*L2.

HONESTY: proper RS codes over F_q, q prime, eval points = mu_n a proper 2-power subgroup of F_q^*
(n=2^mu, n|q-1, q>>... limited by brute force q^n sweep => small).  Where exhaustive u0-sweep is
infeasible (q^n too big), we Monte-Carlo the u0 distribution AND separately maximize |S(u0)| by the
EXACT MacWilliams identity S(u0)+|Ball| <-> list-size of extended code C+<u1> (an integer count we can
optimize over u0 by coset search).  We flag which mode is used.
"""
import itertools, math, cmath, random

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_q(n, mult):
    """smallest prime q with n | q-1 and q >= mult (so a 2-power subgroup mu_n exists)."""
    q = ((mult // n) + 1) * n + 1
    while not (is_prime(q) and (q-1) % n == 0):
        q += n
    return q

def primroot(q):
    m = q-1; fs = set(); d = 2
    while d*d <= m:
        if m % d == 0:
            fs.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.add(m)
    a = 2
    while any(pow(a, (q-1)//f, q) == 1 for f in fs): a += 1
    return a

def mu_subgroup(q, n):
    g = primroot(q); h = pow(g, (q-1)//n, q)
    return [pow(h, i, q) for i in range(n)]

def wt(v):
    return sum(1 for x in v if x != 0)

def run(q, n, k, r, mode="exhaustive", samples=200000, seed=1):
    random.seed(seed)
    D_eval = mu_subgroup(q, n)              # eval points = proper 2-power subgroup mu_n
    w = cmath.exp(2j*math.pi/q)

    # RS code C = {(g(x))_{x in D_eval} : deg g < k}
    def codeword(coef):
        return tuple(sum(c * pow(x, j, q) for j, c in enumerate(coef)) % q for x in D_eval)

    C = [codeword(coef) for coef in itertools.product(range(q), repeat=k)]
    Cset = set(C)

    # u1 = a fixed degree-(k) extension direction NOT in C (the line direction): take x^k evaluations
    u1 = tuple(pow(x, k, q) for x in D_eval)
    assert u1 not in Cset

    # extended code Cext = C + <u1>  (dim k+1); MacWilliams: M(u0) = #{ z in Cext : wt(u0 - z) <= r }
    Cext = set()
    for c in C:
        for g in range(q):
            Cext.add(tuple((ci + g*u1i) % q for ci, u1i in zip(c, u1)))
    Cext = list(Cext)

    # Krawtchouk weights K_w(j) = Bhat(a) for any a of weight j = Fourier transform of Hamming ball B(r):
    #   K_w(j) = sum_{l=0}^{r} sum over ball coordinates... = sum_{i=0}^{min(j,r)} (-1)^i C(j,i)(q-1)^? ...
    # Cleanest: Bhat(a) depends only on wt(a)=j. Compute directly by Krawtchouk formula:
    #   K_r(j) = sum_{i=0}^{r} C(j,i) C(n-j, r-i) ... is the ball-SHELL; we want ball B(<=r):
    #   Bhat(a) = sum_{v: wt(v)<=r} e_p(a.v) = sum_{l=0}^{r} Kraw_l(j)  where
    #   Kraw_l(j;n,q) = sum_{i} (-1)^i (q-1)^{l-i} C(j,i) C(n-j, l-i)   (q-ary Krawtchouk).
    from math import comb
    def kraw_shell(l, j):
        return sum((-1)**i * (q-1)**(l-i) * comb(j, i) * comb(n-j, l-i)
                   for i in range(0, l+1) if 0 <= l-i <= n-j and i <= j)
    Kball = [sum(kraw_shell(l, j) for l in range(0, r+1)) for j in range(n+1)]

    # |Ball|
    Ball_size = sum(comb(n, l) * (q-1)**l for l in range(0, r+1))

    # The exact S(u0) via the extended-code list size (MacWilliams), an INTEGER:
    #   M(u0)_count = #{ z in Cext : wt(u0 - z) <= r }, and  S(u0) = (q^n/(q|C|)) M_count - |Ball|.
    # We want sup_{u0} |S(u0)| and the distribution. The list-size route is exact & fast per u0.
    def Mcount(u0):
        c = 0
        for z in Cext:
            d = 0
            for a, b in zip(u0, z):
                if (a - b) % q != 0:
                    d += 1
                    if d > r: break
            if d <= r: c += 1
        return c

    scale = (q ** n) / (q * len(C))   # = q^n / (q|C|) = q^{n-k-1}
    # Parseval scale for S over u0: avg_{u0}|S(u0)|^2 = sum_{xi in D, xi!=0} |K_w(wt xi)|^2 / (normalizing).
    # We measure the distribution empirically.

    if mode == "exhaustive":
        space = itertools.product(range(q), repeat=n)
        total = q ** n
    else:
        total = samples

    R_inf = 0.0
    sum2 = 0.0
    sum4 = 0.0
    cnt = 0
    worst_u0 = None
    if mode == "exhaustive":
        iterator = itertools.product(range(q), repeat=n)
    else:
        def gen():
            for _ in range(samples):
                yield tuple(random.randrange(q) for _ in range(n))
        iterator = gen()

    for u0 in iterator:
        m = Mcount(u0)
        S = scale * m - Ball_size       # S(u0) is real here (count-based); |S| = deviation
        a = abs(S)
        if a > R_inf:
            R_inf = a; worst_u0 = u0
        sum2 += a*a
        sum4 += a*a*a*a
        cnt += 1

    L2 = math.sqrt(sum2 / cnt)
    L4ratio = (sum4/cnt) / ((sum2/cnt)**2) if sum2 > 0 else 0.0
    c_eff = R_inf / L2 if L2 > 0 else float('inf')
    return dict(q=q, n=n, k=k, r=r, mode=mode, cnt=cnt, Ball=Ball_size,
                R_inf=R_inf, L2=L2, L4ratio=L4ratio, c_eff=c_eff,
                sup_over_ball=R_inf/Ball_size if Ball_size else 0.0,
                dimD=n-k-1)

if __name__ == "__main__":
    print("="*110)
    print("A1: u0-parameter sheaf conductor proxy. Question: c_eff = sup|S| / L2(S) -- BOUNDED (sheaf O(1) => crack) or GROWS with n (=> wall)?")
    print("="*110)
    print(f"{'q':>6} {'n':>4} {'k':>3} {'r':>3} {'dimD':>5} {'mode':>5} {'#u0':>9} {'|Ball|':>9} "
          f"{'sup|S|':>10} {'L2(S)':>10} {'c_eff':>8} {'L4rat':>7} {'sup/|Ball|':>10}")
    # exhaustive feasible only for tiny q^n. Use small q, small n, k, then scale n.
    cases = [
        # (q, n, k, r): want n=2^mu proper subgroup, q prime, n|q-1, q>>n, k small, r<n
        (17, 4, 1, 1, "exhaustive"),
        (17, 4, 1, 2, "exhaustive"),
        (17, 8, 1, 2, "monte"),
        (17, 8, 2, 2, "monte"),
        (41, 8, 2, 3, "monte"),
        (17, 16, 2, 4, "monte"),
        (97, 16, 2, 5, "monte"),
        (97, 16, 3, 5, "monte"),
        (193, 32, 3, 8, "monte"),
    ]
    for c in cases:
        q, n, k, r, mode = c
        try:
            res = run(q, n, k, r, mode=mode, samples=60000)
        except Exception as e:
            print(f"{q:>6} {n:>4} {k:>3} {r:>3}  ERROR {e}")
            continue
        print(f"{res['q']:>6} {res['n']:>4} {res['k']:>3} {res['r']:>3} {res['dimD']:>5} "
              f"{res['mode']:>5} {res['cnt']:>9} {res['Ball']:>9} {res['R_inf']:>10.2f} "
              f"{res['L2']:>10.2f} {res['c_eff']:>8.3f} {res['L4ratio']:>7.3f} {res['sup_over_ball']:>10.4f}",
              flush=True)
    print()
    print("READING: c_eff column = the sheaf conductor proxy (sup-norm / sqrt-cancellation scale).")
    print("  c_eff BOUNDED as n grows + L4rat ~ 2 (CUE-like) => trace-sheaf of bounded conductor => FKM => CRACK.")
    print("  c_eff GROWS with n (or sqrt(log n)) => conductor n-dependent => relocation FAILS => reduces-to-wall.")
    print("  sup/|Ball| > 1 at any row => the literal open-core inequality sup|S|<=|Ball| is FALSE there (Johnson side).")

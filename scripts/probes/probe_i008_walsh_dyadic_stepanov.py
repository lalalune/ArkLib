#!/usr/bin/env python3
"""
PROBE [I008] — Walsh/Haar-packet DYADIC-TOWER Stepanov auxiliary for M(mu_n).

THE OBJECT (campaign open core, intrinsic, do not relocate):
    M(mu_n) = max_{b != 0} | Sum_{x in mu_n} e_p(b x) |,
    mu_n = 2-power multiplicative subgroup of F_p^*, n = 2^mu, n | p-1, p PRIME,
    p >> n^3 (prize regime p ~ n^beta, beta in [4,5]; NEVER n = p-1).
TARGET prize floor: M(mu_n) <= C sqrt(n log(p/n)).
Known SOTA in this regime: M <= n^{1-o(1)} (BGK, ineffective). Gap to close: exponent 1 -> 1/2.

THE IDEA [I008] (stepanov-2adic, novelty 9): coordinatize x in mu_n by its 2-adic
digit vector (mu_n is cyclic of order 2^mu, x = g^j, j in Z/2^mu, digits of j). Build a
Walsh-packet / dyadic-tower auxiliary
    Q(X) = prod_{i=1}^{mu} ( X^{2^{i-1}} - s_i )
so that (claim) "vanishing to high order on mu_n is achieved by tower telescoping: each
factor kills one dyadic level; order ~ mu at LINEAR degree (not n/r)."
NEW LEMMA claimed: exists Q, deg Q = O(n/log n), vanishing to ORDER >= log n on mu_n,
giving via Stepanov |mu_n cap (shift)| <= O(n/(log n)^2), summing cosets => M <= sqrt(n log n).

WHAT STEPANOV ACTUALLY CONSUMES:
    |{ x in mu_n : Q(x)=0 }| * M  <=  deg Q,
where M = the VANISHING MULTIPLICITY (order of contact) common to all counted roots,
i.e. (X - x0)^M | Q for each counted root x0. A sub-Johnson bound needs deg Q = O(n/log n)
AND M >= log n simultaneously, at the SAME points.

THE SUSPECTED HORN (why this is the C27-telescope confusion, multiplicity edition):
A product of (X^{2^{i-1}} - s_i) gives MANY roots spread across nested subgroups (telescoping
in the # of roots / across DYADIC LEVELS = different points), NOT high ORDER (multiplicity)
at a SINGLE point. mu_n consists of SIMPLE roots of the separable X^n - 1 (char p, p nmid n);
in-tree theorem mu_n_roots_simple proves (X - z)^2 nmid (X^n - 1). Any auxiliary Q that one
can actually build that vanishes ON mu_n inherits multiplicity 1 at those points unless Q has
the (X^n-1)^M structure, which costs degree M*n, not linear. So we expect:
    actual vanishing multiplicity of Q at its mu_n roots = 1  (NOT log n),
    => Stepanov gives only |Z| <= deg Q  (trivial), no sqrt saving.

THIS PROBE measures, over genuine proper mu_n (p prime, p >> n^3, p-1 div by n=2^mu),
EXACTLY (sympy over GF(p)):
  (1) the dyadic-tower Q = prod_{i}(X^{2^{i-1}} - s_i): its root count on mu_n and the
      ACTUAL vanishing multiplicity at each such root (order of contact).
  (2) the resulting Stepanov bound |Z| <= deg Q / M_min, vs trivial n and Johnson sqrt(n).
  (3) the BEST possible: over ALL choices of shifts s_i in mu_n / in F_p, can ANY product
      of this form achieve M >= 2 at a mu_n point at sub-n degree? (multiplicity audit)
  (4) cross-check against the true M(mu_n) computed by FFT-free direct sum.

HONEST verdict criteria:
  real-handle    : some dyadic-tower Q achieves M >= 2 at its mu_n roots at deg = O(n/log n),
                   yielding |Z| (and hence M(mu_n)) strictly below n^{1-eps} for measured eps>0.
  promising-part : multiplicity stays 1 but the IDENTITY structure suggests a different lever.
  no-gain        : multiplicity pinned to 1 (telescoping makes roots, not order); Stepanov
                   collapses to deg Q >= n; never beats trivial, let alone Johnson.
  refuted        : the claimed lemma is provably false (a counterexample construction).
"""
import sympy
from sympy import GF, Poly, symbols, factorint
import math, sys, functools
print = functools.partial(__builtins__.print if hasattr(__builtins__, 'print') else __builtins__['print'], flush=True)

X = symbols('X')

def is_prime(m): return sympy.isprime(m)

def find_prime_pow2(mu, beta):
    """Smallest prime p with n=2^mu | p-1 and p ~ n^beta (p >> n^3)."""
    n = 1 << mu
    target = int(n ** beta)
    # p = k*n + 1, choose k so p ~ target, p prime
    k0 = max(2, target // n)
    k = k0
    while True:
        p = k * n + 1
        if is_prime(p) and p > n**3:
            return p, n
        k += 1

def subgroup(p, n):
    """The 2-power subgroup mu_n = {g^i} of order n in F_p^*."""
    # find element of order exactly n
    for g0 in range(2, p):
        g = pow(g0, (p - 1) // n, p)
        S = set()
        x = 1
        for _ in range(n):
            S.add(x); x = (x * g) % p
        if len(S) == n:
            return sorted(S), g
    raise RuntimeError("no generator")

def true_M(H, p):
    """True M(mu_n) = max_{b!=0} |sum_{x in H} e_p(b x)| by direct evaluation."""
    tp = 2 * math.pi
    B = 0.0
    bestb = 0
    for b in range(1, p):
        c = 0.0; s = 0.0
        for x in H:
            ang = tp * ((b * x) % p) / p
            c += math.cos(ang); s += math.sin(ang)
        m = math.hypot(c, s)
        if m > B: B = m; bestb = b
    return B, bestb

def dyadic_tower_poly(mu, shifts, p):
    """Q(X) = prod_{i=1}^{mu} (X^{2^{i-1}} - s_i) over GF(p)."""
    dom = GF(p)
    Q = Poly(1, X, domain=dom)
    for i in range(1, mu + 1):
        e = 1 << (i - 1)
        Q = Q * Poly(X**e - shifts[i - 1], X, domain=dom)
    return Q

def root_mult(Q, x0, p):
    """Vanishing multiplicity (order of contact) of Q at x0 in F_p: largest M with (X-x0)^M | Q."""
    dom = GF(p)
    lin = Poly(X - x0, X, domain=dom)
    M = 0
    R = Q
    while True:
        q, r = sympy.div(R, lin, X, domain=dom)
        if r.is_zero:
            M += 1; R = q
        else:
            break
    return M

def analyze(mu, beta):
    p, n = find_prime_pow2(mu, beta)
    H, g = subgroup(p, n)
    Hset = set(H)
    print(f"\n=== mu={mu}  n=2^mu={n}  p={p} (prime)  p/n^3={p/n**3:.1f}  beta_eff={math.log(p)/math.log(n):.2f} ===")

    # (1) The "natural" dyadic-tower auxiliary: shifts taken as powers of a fixed mu_n element.
    # The construction wants each factor (X^{2^{i-1}} - s_i) to "kill dyadic level i".
    # Try shifts s_i = 1 (factors X^{2^{i-1}} - 1, which vanish on the level-i sub-subgroup mu_{2^{i-1}})
    # and s_i = an element of mu_n (a "shift").
    for label, shifts in [
        ("s_i=1 (sub-subgroup tower)", [1] * mu),
        ("s_i=g^i (mu_n shifts)",      [pow(g, i, p) for i in range(1, mu + 1)]),
        ("s_i=g (fixed nontrivial)",   [g] * mu),
    ]:
        Q = dyadic_tower_poly(mu, shifts, p)
        deg = Q.degree()
        # roots of Q lying in mu_n, with multiplicities
        mults = {}
        for x0 in H:
            m = root_mult(Q, x0, p)
            if m > 0:
                mults[x0] = m
        Z = len(mults)
        Mmin = min(mults.values()) if mults else 0
        Mmax = max(mults.values()) if mults else 0
        # Stepanov bound: |Z| <= deg / Mmin (only valid if common mult Mmin used)
        steb = (deg / Mmin) if Mmin else float('inf')
        print(f"  [{label}]  degQ={deg}  #roots_on_mu_n={Z}  mult(min/max)={Mmin}/{Mmax}"
              f"  Stepanov|Z|<= deg/M={steb:.1f}  (trivial n={n}, Johnson~{math.sqrt(n):.1f})")

    # (3) MULTIPLICITY AUDIT: can ANY product of (X^{2^{i-1}} - s_i), s_i in F_p, achieve
    # multiplicity >= 2 at a point of mu_n? (the lemma's core requirement)
    # A point x0 in mu_n is a root of (X^{2^{i-1}} - s_i) iff s_i = x0^{2^{i-1}}.
    # Multiplicity of (X^{2^{i-1}} - s_i) at x0 is 1 unless deriv 2^{i-1} X^{2^{i-1}-1}=0 at x0,
    # i.e. unless 2^{i-1} = 0 mod p (impossible: p odd) or x0=0 (not in mu_n).
    # So EACH factor contributes mult exactly 1 if it hits x0, 0 otherwise.
    # Total mult at x0 = #{i : s_i = x0^{2^{i-1}}}. To get >=2, need two indices i<j with
    # s_i = x0^{2^{i-1}} and s_j = x0^{2^{j-1}} simultaneously -- always achievable by CHOOSING
    # s_i, s_j for that ONE x0, BUT then check it across the whole counted set.
    print("  -- multiplicity-mechanism audit (per-factor order at a mu_n point) --")
    x0 = H[1] if len(H) > 1 else H[0]
    orders = []
    for i in range(1, mu + 1):
        e = 1 << (i - 1)
        s = pow(x0, e, p)  # force factor i to vanish at x0
        # multiplicity of (X^e - s) at x0:
        Qi = Poly(X**e - s, X, domain=GF(p))
        orders.append(root_mult(Qi, x0, p))
    print(f"     per-factor multiplicity at a forced common root x0: {orders}"
          f"  (sum if ALL forced at SAME x0 = {sum(orders)} at deg {sum(1<<(i-1) for i in range(1,mu+1))})")
    # If we force ALL mu factors to vanish at the SAME x0 (s_i = x0^{2^{i-1}}), what is the
    # multiplicity at x0, and how many OTHER mu_n points are then also roots?
    shifts_all = [pow(x0, 1 << (i - 1), p) for i in range(1, mu + 1)]
    Qall = dyadic_tower_poly(mu, shifts_all, p)
    deg = Qall.degree()
    mults = {x: root_mult(Qall, x, p) for x in H if root_mult(Qall, x, p) > 0}
    Z = len(mults)
    Mx0 = mults.get(x0, 0)
    Mmin = min(mults.values()) if mults else 0
    print(f"     ALL factors forced to vanish at x0: mult(x0)={Mx0}  #roots_on_mu_n={Z}"
          f"  min-mult-over-roots={Mmin}  degQ={deg}")
    print(f"     => Stepanov common-multiplicity bound |Z| <= deg/Mmin = {deg/Mmin if Mmin else float('inf'):.1f}"
          f"  (need < n={n} to be nontrivial; < sqrt(n)~{math.sqrt(n):.1f} for prize)")

    # (4) true M for sanity (only small p)
    if p < 200000:
        B, bb = true_M(H, p)
        print(f"  true M(mu_n) = {B:.3f}  (sqrt(n)={math.sqrt(n):.3f}, sqrt(2n ln(p/n))={math.sqrt(2*n*math.log(p/n)):.3f},"
              f" n^{{0.9}}={n**0.9:.1f})  exponent log(M)/log(n)={math.log(B)/math.log(n):.3f}")

if __name__ == "__main__":
    print("PROBE [I008]: Walsh/dyadic-tower Stepanov auxiliary -- does telescoping make ORDER or just ROOTS?")
    print("Stepanov needs COMMON vanishing MULTIPLICITY M>=log n at deg O(n/log n). Measuring actual M.")
    for mu in [3, 4, 5, 6]:
        analyze(mu, beta=4.0)
    # one larger-mu structural check (no true_M, too big) to see multiplicity scaling
    analyze(7, beta=4.0)


def n_of(mu): return 1 << mu

def mult_at(x0, shifts, mu, p):
    """EXACT multiplicity of Q=prod_i(X^{2^{i-1}}-s_i) at x0 in F_p^*.
    Each factor (X^e - s_i), e=2^{i-1}, has DERIVATIVE e*X^{e-1} nonzero at x0!=0 (p odd, e=2^{i-1} a
    UNIT mod p), so x0 is a SIMPLE root of factor i iff x0^e == s_i, else not a root. Hence
    mult_Q(x0) = #{i : s_i == x0^{2^{i-1}} mod p}. (Telescoping adds factors that share x0, but each
    is simple; no factor can contribute order>1 because mu_n roots are separable.)"""
    return sum(1 for i in range(1, mu + 1) if shifts[i - 1] == pow(x0, 1 << (i - 1), p))

def root_set_with_mult(shifts, mu, p, H):
    d = {}
    for x0 in H:
        m = mult_at(x0, shifts, mu, p)
        if m > 0: d[x0] = m
    return d

def best_common_mult(mu, p):
    """DECISIVE & EXACT (closed-form multiplicity, no sympy loop): over ALL shift vectors
    s_i in F_p (the most generous version of the lemma -- not even restricted to mu_n),
    the MAX achievable COMMON multiplicity = min over the mu_n root set. The lemma needs
    common-mult >= log n at deg O(n/log n).  We search shifts over mu_n (the structured
    choices) exhaustively via the closed-form mult; this is fast (no polynomial division)."""
    import itertools
    H, g = subgroup(p, n_of(mu))
    best = (1, None, mu, 1)  # (common_mult, shifts, deg, nroots)
    for shifts in itertools.product(H, repeat=mu):
        d = root_set_with_mult(shifts, mu, p, H)
        if not d: continue
        cm = min(d.values())
        deg = sum(1 << (i - 1) for i in range(1, mu + 1))  # n-1, fixed by the tower
        if (cm, len(d)) > (best[0], best[3]):
            best = (cm, shifts, deg, len(d))
    return best

# sanity: closed-form mult matches sympy polynomial division on a small case
def _sanity(mu=3):
    p, n = find_prime_pow2(mu, 4.0)
    H, g = subgroup(p, n)
    shifts = [pow(H[1], 1 << (i - 1), p) for i in range(1, mu + 1)]  # all forced at H[1]
    Q = dyadic_tower_poly(mu, shifts, p)
    ok = all(mult_at(x0, shifts, mu, p) == root_mult(Q, x0, p) for x0 in H)
    print(f"  [sanity mu={mu}] closed-form multiplicity == sympy poly-division multiplicity: {ok}")

print("\n\n==== DECISIVE: best achievable COMMON multiplicity over dyadic-tower products (s_i in mu_n) ====")
print("(common mult = min over the mu_n root set = the ONLY thing Stepanov can use; closed-form, exact)")
_sanity(3)
for mu in [3, 4]:   # exhaustive shift search over mu_n^mu (32^5=33M too slow; mu>=5 covered by proof below)
    p, n = find_prime_pow2(mu, 4.0)
    cm, shifts, deg, nroots = best_common_mult(mu, p)
    print(f"  mu={mu} n={n} p={p}: BEST common-mult={cm} over {nroots} roots, degQ={deg}"
          f"  => Stepanov |Z| <= deg/cm = {deg/cm:.1f}  (trivial n={n}; prize needs <<sqrt(n)={math.sqrt(n):.1f})")
    print(f"     log2 n = {mu} (lemma WANTS common-mult >= {mu}); BEST achievable = {cm}. "
          f"{'CLAIM HOLDS' if cm >= mu else 'CLAIM FAILS: best common-mult is '+str(cm)+' (NOT log n)'}")

print("\n  THE STRUCTURAL REASON (closed-form): mult_Q(x0)=#{i: s_i=x0^{2^{i-1}}} since every factor")
print("  (X^{2^{i-1}}-s_i) has a UNIT derivative at x0!=0, so contributes order EXACTLY 1 where it")
print("  vanishes. To get common-mult m on Z roots you need each of the Z roots hit by >= m of the")
print("  mu factors: sum of factor-root-counts >= m*Z. Factor i has <= gcd(2^{i-1},n)=2^{i-1} roots")
print("  in mu_n, so total roots-with-mult = sum_i 2^{i-1} = n-1 = deg Q. Thus m*Z <= deg Q = n-1,")
print("  which is EXACTLY the trivial Stepanov inequality |Z| <= deg Q / m. The product buys NOTHING")
print("  beyond deg = n-1: telescoping spreads the n-1 simple incidences across roots/levels, it does")
print("  NOT concentrate them into multiplicity. Same wall as mu_n_roots_simple / C27 (house!=norm).")

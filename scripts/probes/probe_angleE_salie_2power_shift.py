#!/usr/bin/env python3
"""
ANGLE E (issue #444): does the 2-power-order multiplicative character chi give the shifted
subgroup sum  S(k) = sum_{x in mu_n} chi^k(x+1)  a SALIE-type EXPLICIT evaluation / genuine
sqrt(n) cancellation that GENERIC-order characters lack?

WHY THIS MIGHT WORK (the lead).  Salie sums S(a,b)=sum_x leg(x) e_p(ax+b/x) evaluate EXACTLY
(|S| in {0, 2 sqrt p}) because the QUADRATIC Gauss sum is explicit (g(leg)=+-sqrt(p) or
+-i sqrt(p)).  chi of order m=2^mu has a 2-power TOWER of Gauss sums g(chi), g(chi^2),...,
g(chi^{m/2})=g(leg).  Hasse-Davenport / Gross-Koblitz relate consecutive levels.  If the shift
sum S(k) for k a 2-power decomposes into a PRODUCT/SUM of Gauss sums whose magnitudes are each
EXACTLY sqrt(p) (Davenport-Hasse) AND the subgroup-restriction does not destroy that, we'd get an
EXPLICIT |S(k)| = c*sqrt(n)-ish, off the BGK wall.

THE OBJECT, made precise.  mu_n = {2^mu-th roots of unity} subset F_p^* (n | p-1, p prime, p>>n^3,
thin n <= p^{1/4}).  chi : F_p^* -> C^* a FIXED multiplicative character of order m=n (the natural
"dyadic" character cutting out mu_n as its kernel-coset structure).  For exponent k:
    S(k) := sum_{x in mu_n} chi^k(x + 1)        (convention chi^k(0)=0)
We compare:
  (A) k = 2^j (the 2-POWER shifts) -- the lead's special exponents.
  (B) generic k (odd / random) -- the control.
Claim under test: |S(2^j)| takes a SMALL DISCRETE set of values clustered at integer multiples of
sqrt(n) (Salie-like), while generic |S(k)| SPREADS continuously up to the BGK envelope.

WE ALSO test the alternative reading of "the shift sum": the FULL-FIELD analogue (Jacobi/Gauss
exact) and the additive-period eta_b control, to be sure which object (if any) is Salie.

HONESTY.  Pure stdlib (no numpy/sympy): exact mod-p arithmetic, cmath for magnitudes.
p PRIME, n=2^mu, n | p-1, p ~ n^beta beta in [4,5] (thin), NEVER n=p-1.
Tag each finding measured-small-n / proven / refuted.  A "partial prize" = |S(2^j)| == c*sqrt(n)
EXACTLY (discrete, p-stable up to phase) while generic k spreads.
"""
import cmath, math, itertools, random

# ---------------- pure-stdlib number theory ----------------
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def factorize(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1
    facs = list(factorize(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

def find_prime(n, beta):
    """smallest prime p ~ n^beta with n | p-1 and (p-1)//n > 1 (so mu_n proper)."""
    target = int(n ** beta)
    cand = target - (target % n) + 1
    if cand <= target: cand += n
    while True:
        if is_prime(cand) and (cand - 1) % n == 0 and (cand - 1) // n > 1:
            return cand
        cand += n

# ---------------- the structures ----------------
def mu_n(n, p, g=None):
    """the 2^mu-th roots of unity in F_p^*; contains -1 for n even (dyadic)."""
    if g is None: g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    sub = []; x = 1
    for _ in range(n):
        sub.append(x); x = x * h % p
    assert len(set(sub)) == n
    assert (p - 1) in sub, "mu_n should contain -1 == p-1"
    return sub

def char_values(p, g, m):
    """multiplicative character chi of order m: chi(g^a) = zeta_m^a, via discrete log.
    Returns a dict val[x in F_p^*] = integer e in [0,m) so chi(x) = exp(2pi i e / m).
    (m must divide p-1.)"""
    assert (p - 1) % m == 0
    # discrete log table base g
    dl = [0] * p
    x = 1
    for a in range(p - 1):
        dl[x] = a; x = x * g % p
    # chi(x) = zeta_m ^ (dl[x] * ((p-1)//m) / (p-1) * m)  -> exponent e = dl[x] mod m  when m|p-1
    # order-m char: chi(g) = zeta_m, so chi(g^a)=zeta_m^a => e = dl[x] mod m.
    expo = [None] * p  # expo[x] in [0,m) or None for x=0
    for x in range(1, p):
        expo[x] = dl[x] % m
    return expo  # chi(x) = cmath.exp(2j*pi*expo[x]/m)

def chi_pow(expo, m, x, k):
    """chi^k(x) as a complex number; chi^k(0)=0."""
    if x % 1 != 0: raise ValueError
    x = int(x)
    if x == 0: return 0+0j
    e = expo[x]
    if e is None: return 0+0j
    return cmath.exp(2j * math.pi * (e * k % m) / m)

# ---------------- the shift sum S(k) = sum_{x in mu_n} chi^k(x+1) ----------------
def shift_sum(sub, expo, m, p, k):
    s = 0+0j
    for x in sub:
        s += chi_pow(expo, m, (x + 1) % p, k)
    return s

# additive period control: eta_b = sum_{x in mu_n} e_p(b x)
def eta_b(sub, p, b):
    s = 0+0j; w = 2 * math.pi / p
    for x in sub:
        s += cmath.exp(1j * w * ((b * x) % p))
    return s

# ---------------- Gauss sum (for the tower context) ----------------
def gauss_sum(expo, m, p, k):
    """g(chi^k) = sum_{x!=0} chi^k(x) e_p(x).  |g|=sqrt(p) for chi^k nontrivial, =-1 for trivial."""
    s = 0+0j; w = 2 * math.pi / p
    for x in range(1, p):
        s += chi_pow(expo, m, x, k) * cmath.exp(1j * w * x)
    return s

# ======================================================================
def banner(t): print("=" * 84); print(t); print("=" * 84)

def T1_shiftsum_2power_vs_generic():
    banner("T1: |S(k)| for k = 2^j (2-power shifts) vs generic k  -- Salie-discrete or spread?")
    print("   S(k) = sum_{x in mu_n} chi^k(x+1),  chi order m = n (the dyadic character).")
    print("   Salie-prize signature: |S(2^j)| in a SMALL discrete set ~ c*sqrt(n); generic k SPREADS.\n")
    for n in (8, 16, 32):
        p = find_prime(n, 4.0); g = primitive_root(p)
        m = n
        sub = mu_n(n, p, g)
        expo = char_values(p, g, m)
        sqn = math.sqrt(n)
        twopow = [k for k in range(1, m) if (k & (k - 1)) == 0]  # 1,2,4,...
        generic = [k for k in range(1, m) if (k & (k - 1)) != 0 and k % 2 == 1]  # odd non-2power
        def mags(ks):
            return sorted(round(abs(shift_sum(sub, expo, m, p, k)), 4) for k in ks)
        tp = mags(twopow); gn = mags(generic[: max(6, len(twopow))])
        # ratios to sqrt(n)
        print(f" n={n} p={p}  sqrt(n)={sqn:.3f}  2sqrt(n)={2*sqn:.3f}")
        print(f"   2-power k={twopow}:")
        print(f"     |S|        = {[f'{v:.3f}' for v in tp]}")
        print(f"     |S|/sqrt n = {[f'{v/sqn:.3f}' for v in tp]}")
        if gn:
            print(f"   generic odd k (sample {generic[:len(gn)]}):")
            print(f"     |S|        = {[f'{v:.3f}' for v in gn]}")
            print(f"     |S|/sqrt n = {[f'{v/sqn:.3f}' for v in gn]}")
        # distinctness within 2-power class
        dtp = len(set(tp)); print(f"   distinct |S| among 2-power k: {dtp} (of {len(twopow)})")

def T2_full_distribution_and_envelope():
    banner("T2: full |S(k)| distribution over ALL k -- where do 2-power k sit vs the max (BGK envelope)?")
    print("   If 2-power k are SYSTEMATICALLY the SMALL ones (~sqrt n) and the MAX is at generic k,")
    print("   then 2-power shifts have extra cancellation. If 2-power k can also be LARGE, no special.\n")
    for n in (8, 16, 32):
        p = find_prime(n, 4.0); g = primitive_root(p); m = n
        sub = mu_n(n, p, g); expo = char_values(p, g, m)
        sqn = math.sqrt(n)
        allk = list(range(1, m))
        vals = {k: abs(shift_sum(sub, expo, m, p, k)) for k in allk}
        mx = max(vals.values()); mn_nz = min(v for v in vals.values() if v > 1e-9) if any(v>1e-9 for v in vals.values()) else 0
        twopow = [k for k in allk if (k & (k - 1)) == 0]
        tp_vals = sorted(vals[k] for k in twopow)
        argmax_k = max(vals, key=vals.get); argmax_is_2pow = (argmax_k & (argmax_k-1)) == 0
        print(f" n={n} p={p}: max|S|={mx:.3f} ({mx/sqn:.3f} sqrt n) at k={argmax_k} "
              f"({'2-POWER' if argmax_is_2pow else 'non-2-power'}); min nonzero={mn_nz:.3f}")
        print(f"   2-power |S|/sqrt n = {[f'{v/sqn:.3f}' for v in tp_vals]}  (max over 2-power "
              f"= {max(tp_vals)/sqn:.3f} sqrt n)")
        # rank of largest 2-power among all
        order = sorted(vals.values(), reverse=True)
        rank = order.index(max(tp_vals)) + 1
        print(f"   largest 2-power |S| ranks #{rank} of {len(allk)} (1=overall max).")

def T3_p_stability_of_2power_shift():
    banner("T3: p-STABILITY of |S(2^j)| across primes -- discrete-value (Salie) or p-dependent (BGK)?")
    print("   Salie values are p-stable in /sqrt(p)-normalization. For the SUBGROUP sum, a true")
    print("   explicit evaluation => |S(2^j)|/sqrt(n) STABLE across p; BGK => it WANDERS.\n")
    for n in (8, 16):
        ps = [find_prime(n, 4.0), find_prime(n, 4.3), find_prime(n, 4.6)]
        sqn = math.sqrt(n)
        print(f" n={n}: primes {ps}")
        twopow = [k for k in range(1, n) if (k & (k - 1)) == 0]
        for k in twopow:
            row = []
            for p in ps:
                g = primitive_root(p); sub = mu_n(n, p, g); expo = char_values(p, g, n)
                row.append(abs(shift_sum(sub, expo, n, p, k)) / sqn)
            spread = max(row) - min(row)
            tag = "STABLE" if spread < 0.05 else ("near-stable" if spread < 0.3 else "WANDERS")
            print(f"   k={k:2d}: |S|/sqrt n across p = {[f'{v:.3f}' for v in row]}  spread={spread:.3f} [{tag}]")

def T4_gauss_tower_decomposition():
    banner("T4: does S(2^j) decompose into the 2-power GAUSS-SUM tower (the mechanism)?")
    print("   Classical: sum_{x in mu_n} f(x) = (1/n) sum_{psi: psi^n=1} (n-char) ... For the SHIFT,")
    print("   expand chi^k(x+1) is NOT multiplicative. We instead test the DUAL identity numerically:")
    print("   is |S(k)| explained by Jacobi/Gauss magnitudes (each sqrt p) -- i.e. is S(k)/sqrt(p)")
    print("   an ALGEBRAIC INTEGER of small house (a few roots of unity), vs a Weil-spread real?\n")
    for n in (8, 16):
        p = find_prime(n, 4.0); g = primitive_root(p); m = n
        sub = mu_n(n, p, g); expo = char_values(p, g, m)
        sqp = math.sqrt(p)
        twopow = [k for k in range(1, m) if (k & (k - 1)) == 0]
        print(f" n={n} p={p} sqrt p={sqp:.2f}:")
        for k in twopow:
            S = shift_sum(sub, expo, m, p, k)
            # gauss magnitude reference
            print(f"   k={k:2d}: S={S.real:+.3f}{S.imag:+.3f}i  |S|={abs(S):.3f}  "
                  f"|S|/sqrt(n)={abs(S)/math.sqrt(n):.3f}  |S|/sqrt(p)={abs(S)/sqp:.4f}")
        # Gauss sum tower magnitudes (sanity: each |g|=sqrt p)
        gm = [abs(gauss_sum(expo, m, p, k)) / sqp for k in twopow]
        print(f"   (sanity) |g(chi^k)|/sqrt p for 2-power k = {[f'{v:.3f}' for v in gm]} (all ~1.000 => Gauss tower healthy)")

def T5_eta_control_and_floor():
    banner("T5: CONTROL -- additive period eta_b (the TRUE BGK floor object) for same n, p.")
    print("   Establishes the floor M(n)=max|eta_b| to compare: is the SHIFT sum S(k) genuinely")
    print("   SMALLER (more cancellation) than the additive floor, or the same scale?\n")
    for n in (8, 16, 32):
        p = find_prime(n, 4.0); g = primitive_root(p)
        sub = mu_n(n, p, g)
        h = pow(g, (p - 1) // n, p)
        # coset reps for eta
        seen = set(); reps = []
        for b in range(1, p):
            if b in seen: continue
            reps.append(b); c = b
            for _ in range(n): seen.add(c); c = c * h % p
        M = max(abs(eta_b(sub, p, b)) for b in reps)
        # max shift sum over 2-power k
        expo = char_values(p, g, n)
        twopow = [k for k in range(1, n) if (k & (k - 1)) == 0]
        Sm = max(abs(shift_sum(sub, expo, n, p, k)) for k in twopow)
        sqn = math.sqrt(n)
        print(f" n={n} p={p}: M(n)=max|eta_b|={M:.3f} ({M/sqn:.3f} sqrt n);  "
              f"max|S(2^j)|={Sm:.3f} ({Sm/sqn:.3f} sqrt n)  "
              f"sqrt(n ln(p/n))={math.sqrt(n*math.log(p/n)):.3f}")

if __name__ == '__main__':
    random.seed(7)
    T1_shiftsum_2power_vs_generic()
    T2_full_distribution_and_envelope()
    T3_p_stability_of_2power_shift()
    T4_gauss_tower_decomposition()
    T5_eta_control_and_floor()

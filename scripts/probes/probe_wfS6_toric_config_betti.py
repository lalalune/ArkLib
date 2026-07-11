#!/usr/bin/env python3
r"""#444 LANE S6: Deligne/Weil-II on the CONFIGURATION variety (NOT the Fermat completion).

================================================================================
MISSION (S6).  The campaign's Betti no-go (probe_betti_independent.py) homogenizes
the subgroup constraint u^d = 1 into a FERMAT HYPERSURFACE
      F: c_1 X_1^d + ... + c_{2r} X_{2r}^d = 0  in P^{2r-1},
whose primitive middle Betti B_prim = ((d-1)^{2r}+(d-1))/d ~ (d-1)^{2r} grows
EXPONENTIALLY in r (and in d). That no-go is the campaign's "AG vacuous past r=2".

BUT that is the WRONG variety. The actual configuration variety is
      V_r = { (x_1..x_{2r}) in mu_n^{2r} :  eps_1 x_1 + ... + eps_{2r} x_{2r} = 0 },
      eps_i = +-1 (r pluses, r minuses),
which lives in the TORUS POWER G_m^{2r}, and mu_n is a 0-DIMENSIONAL etale subscheme
(n geometric points each). So V_r is a SLICE of a finite scheme: a 0-dimensional
scheme of degree <= n^{2r-1} (one linear equation drops one "free" coordinate).

KEY CONSEQUENCE (the thing the campaign missed): for a 0-DIMENSIONAL scheme,
Deligne/Weil-II degenerates -- there is NO middle-dimensional cohomology, NO
sqrt(p) error term. Lang-Weil for dim 0 is EXACT:  #V_r(F_p) = (geometric degree)
once p exceeds the (bounded) bad-prime threshold. The "spurious mass" is NOT a
Weil error term at all -- it is the failure of the char-0 count to equal the
geometric F_p-point count, i.e. an ARITHMETIC LIFTING defect.

WHAT THIS PROBE DOES (exact arithmetic, prize-regime p = n^beta, p = 1 mod n):
  (1) Compute the geometric degree of V_r over C (= char-0 count = (2r-1)!! n^r).
  (2) Compute the F_p-count E_r^charp exactly (FFT over the n periods, big-int).
  (3) spur_r(p) = E_r^charp - E_r^char0 >= 0.
  (4) THE TORIC BETTI:  what bounds spur if V_r were positive-dim? The torus
      hyperplane slice  {sum eps_i u_i = 0} in G_m^{2r} has Betti numbers bounded
      by BINOMIALS C(2r, j) (a hyperplane section of a torus -- Adolphson-Sperber /
      Denef-Loeser toric bound), TOTALLY INDEPENDENT of d. Compare the toric
      envelope  B_toric * p^{(2r-2)/2}  to the Fermat envelope  B_prim * p^{r-1}
      and to the MEASURED spur.
  (5) THE DICHOTOMY: report, at prize scale p = n^4, whether
        spur_r  <=  B_toric * p^{r-1}        (toric envelope -- d-FREE!)
      holds, and how it compares to the random rate n^{2r}/p.

If the toric (binomial, d-free) envelope dominates spur where the Fermat envelope
is vacuous, THAT is the S6 finding: the AG bound is NOT vacuous on the correct
variety -- it just needs the toric model, not the projective Fermat completion.

EXACT ARITHMETIC ONLY. p = 1 mod n, p prime, n = 2^a.
================================================================================
"""
import sys
from math import comb, isqrt
from fractions import Fraction

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def find_prime_1modn(n, beta):
    """Smallest prime p >= n^beta with p = 1 mod n (prize regime, p=1 mod n)."""
    target = int(n ** beta)
    # round up to 1 mod n
    p = target - (target % n) + 1
    if p < target: p += n
    while not is_prime(p):
        p += n
    return p

def subgroup_periods_energy(n, p, r):
    r"""EXACT E_r^charp = #{(x,y) in mu_n^{2r}: sum x = sum y mod p}.
    Via the FFT identity: E_r = (1/p) sum_{t in F_p} |g(t)|^{2r}, g(t)=sum_{x in mu_n} e_p(tx).
    g(t) is constant on cosets of mu_n; there are d = (p-1)/n nonzero coset values + the
    t=0 value g(0)=n. We compute |g(t)|^2 exactly as integer:
        |g(t)|^2 = sum_{x,x' in mu_n} e_p(t(x-x')) = sum over differences.
    Then E_r = (1/p)[ n^{2r} + sum over nonzero cosets d_value^... ].
    To keep it EXACT and feasible we compute the multiset {|g(t)|^2 : t} as the
    convolution-count of the mu_n difference set, then raise to r-th power.
    EXACT integer arithmetic via counting the additive energy directly for small/mid n,
    and via the period histogram for larger n."""
    # build mu_n: a generator g of F_p^*, mu_n = {g^{k*d} : k=0..n-1}, d=(p-1)/n
    d = (p - 1) // n
    g = primitive_root(p)
    base = pow(g, d, p)
    mun = []
    cur = 1
    for _ in range(n):
        mun.append(cur)
        cur = cur * base % p
    munset = set(mun)
    # |g(t)|^2 for each t: count_t[v] where v = (x - x') mod p, x,x' in mun.
    # |g(t)|^2 = sum_{v} cnt[v] e_p(t v) is real; but we need sum_t |g(t)|^{2r}.
    # Simpler EXACT route for E_r: directly count r-fold sums.
    # S_r = multiset of (x_1+...+x_r mod p), x_i in mun. E_r = sum_v (#S_r==v)^2.
    from collections import defaultdict
    # iterative r-fold sumset histogram (exact integer counts)
    hist = defaultdict(int)
    hist[0] = 1
    for _ in range(r):
        nh = defaultdict(int)
        for v, c in hist.items():
            for x in mun:
                nh[(v + x) % p] += c
        hist = nh
    E = 0
    for v, c in hist.items():
        E += c * c
    return E

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1
    factors = []
    m = phi
    f = 2
    while f * f <= m:
        if m % f == 0:
            factors.append(f)
            while m % f == 0: m //= f
        f += 1
    if m > 1: factors.append(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")

def double_factorial_odd(r):
    """(2r-1)!! exact."""
    res = 1
    for k in range(1, r+1):
        res *= (2*k - 1)
    return res

def char0_energy(n, r):
    """E_r^char0 = (2r-1)!! * n^r  (Lam-Leung, PROVEN for mu_{2^a})."""
    return double_factorial_odd(r) * (n ** r)

def fermat_betti(d, r):
    """B_prim = ((d-1)^{2r}+(d-1))/d  (the campaign's Fermat-completion Betti)."""
    num = (d-1)**(2*r) + (d-1)
    assert num % d == 0
    return num // d

def toric_betti_envelope(r):
    r"""Total Betti of the hyperplane slice {sum eps_i u_i = 0} of G_m^{2r}.
    The torus G_m^{2r} has total Betti 2^{2r} (sum C(2r,j) = 2^{2r}).
    A single hyperplane section (one linear equation in the u_i) is a (2r-1)-dim
    variety whose total Betti is bounded by the torus's: <= 2^{2r-1} effective,
    but the DELIGNE-relevant (top-weight, middle) Betti of a generic toric
    hypersurface slice is bounded by C(2r, r) (Adolphson-Sperber: the number of
    lattice points / the normalized volume of the Newton polytope of the linear
    form, which is the simplex => binomial). We use B_toric = C(2r, r) as the
    middle-Betti proxy and 2^{2r} as the total-Betti upper bound. BOTH are
    INDEPENDENT of d. Return (middle_proxy, total_upper)."""
    return comb(2*r, r), 2**(2*r)

def main():
    print("="*78)
    print("LANE S6: toric config variety vs Fermat completion -- the d-FREE Betti")
    print("="*78)
    print("\nThe config variety V_r = {x in mu_n^{2r}: sum eps_i x_i = 0} is a SLICE")
    print("of a 0-dim etale scheme mu_n^{2r}. As a finite scheme: degree-bounded, no")
    print("middle cohomology. As a toric hyperplane: Betti = BINOMIAL C(2r,r), d-FREE.")
    print("Compare to Fermat-completion Betti ~ (d-1)^{2r} (the campaign's no-go).\n")

    beta = 4  # prize regime p = n^4
    # n must be a power of 2; keep n small enough that the exact r-fold histogram
    # over F_p is feasible (cost ~ r * n * |support|, |support| <= p). p=n^4 is big,
    # so we cap n where p^... is countable. Use the FFT-free direct histogram only
    # for n where r-fold support fits; otherwise report the structural envelopes.
    configs = [
        (8, 2), (8, 3), (8, 4),
        (16, 2), (16, 3),
        (32, 2),
    ]
    print(f"{'n':>4} {'beta':>5} {'p':>14} {'d':>10} {'r':>3} "
          f"{'E_char0':>14} {'E_charp':>14} {'spur':>14} "
          f"{'spur/rand':>10} {'spur/Toric':>11} {'spur/Fermat':>12}")
    print("-"*78)
    rows = []
    for n, r in configs:
        p = find_prime_1modn(n, beta)
        d = (p - 1) // n
        E0 = char0_energy(n, r)
        try:
            Ep = subgroup_periods_energy(n, p, r)
        except Exception as e:
            print(f"{n:>4} {beta:>5} {p:>14} {d:>10} {r:>3}  SKIP ({e})")
            continue
        spur = Ep - E0
        rand_rate = Fraction(n**(2*r), p)  # spurious mass if mod-p coincidences random
        b_mid, b_tot = toric_betti_envelope(r)
        # toric Deligne envelope on the (2r-1)-dim toric hyperplane: middle weight
        # 2r-2, error <= B_mid * p^{(2r-2)/2} = B_mid * p^{r-1}
        toric_env = b_mid * (p ** (r-1))
        fermat_env = fermat_betti(d, r) * (p ** (r-1))
        s_rand = float(Fraction(spur,1) / rand_rate) if rand_rate != 0 else float('inf')
        s_tor = float(Fraction(spur, toric_env)) if toric_env else float('inf')
        s_fer = float(Fraction(spur, fermat_env)) if fermat_env else float('inf')
        print(f"{n:>4} {beta:>5} {p:>14} {d:>10} {r:>3} "
              f"{E0:>14} {Ep:>14} {spur:>14} "
              f"{s_rand:>10.3e} {s_tor:>11.3e} {s_fer:>12.3e}")
        rows.append((n,r,p,d,E0,Ep,spur,float(rand_rate),toric_env,fermat_env))

    print("\n" + "="*78)
    print("STRUCTURAL ENVELOPE COMPARISON (d-free toric vs d-blowup Fermat), prize p=n^4")
    print("="*78)
    print(f"{'r':>3} {'C(2r,r)=B_toric':>16} {'2^{2r}=Btot':>12} "
          f"{'(d-1)^{2r}-scale':>18}")
    print("-"*78)
    for r in range(2, 8):
        b_mid, b_tot = toric_betti_envelope(r)
        # at prize d = (p-1)/n ~ n^3 (since p=n^4, d~n^3); use n=2^30 => d~2^90
        d_prize = 2**90
        log2_fermat = 2*r * 90  # log2((d-1)^{2r}) ~ 2r*90
        print(f"{r:>3} {b_mid:>16} {b_tot:>12} {'2^'+str(log2_fermat):>18}")

    print("\nKEY: B_toric = C(2r,r) is bounded by 4^r (Stirling), INDEPENDENT of d.")
    print("Fermat B_prim ~ (d-1)^{2r} = 2^{2r*90} at prize d~2^90: vacuously huge.")
    print("=> IF the relevant variety is the toric slice (0-dim/hyperplane), the AG")
    print("   bound is NOT vacuous: B_toric * p^{r-1} with B_toric = C(2r,r) <= 4^r.")

    # The honest test: does spur actually sit at/below the toric envelope?
    print("\n" + "="*78)
    print("VERDICT (measured spur vs toric envelope at small-n prize-regime points)")
    print("="*78)
    if rows:
        worst_tor = max(r[6] / r[8] for r in rows if r[8])
        worst_fer = max(r[6] / r[9] for r in rows if r[9])
        worst_rand = max(r[6] / (r[3+1] if False else (r[4+1]/1)) for r in rows) if False else None
        all_below_tor = all(r[6] <= r[8] for r in rows)
        print(f"  max spur/Toric-envelope = {worst_tor:.4e}  (toric bound HOLDS = {all_below_tor})")
        print(f"  max spur/Fermat-envelope = {worst_fer:.4e}  (Fermat loose by {1/worst_fer:.2e}x)")
        # is spur tracking random rate (n^{2r}/p)?
        print("\n  spur vs RANDOM rate n^{2r}/p (the actual lifting-defect scale):")
        for (n,r,p,d,E0,Ep,spur,rr,te,fe) in rows:
            print(f"    n={n:>3} r={r}: spur={spur}, rand={rr:.4e}, "
                  f"spur/rand={spur/rr:.4e}, spur/toric={spur/te:.4e}")

if __name__ == "__main__":
    main()

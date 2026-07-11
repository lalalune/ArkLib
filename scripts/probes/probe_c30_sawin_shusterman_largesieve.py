#!/usr/bin/env python3
"""
ATTACK on CONJECTURE C30 (issue #444): "Sawin-Shusterman Large Sieve for Gauss Sums
(orthogonality over the family)". CLAIM: apply the large sieve / orthogonality over the
Gauss-sum family to bound the second moment and claim an AMPLIFIED version reaches the
MAX  max_c |eta_c|  PAST Johnson rather than just the sqrt(n) average.

OBJECT.  Proper subgroup mu_n < F_p^*  (n = 2^mu, n | p-1, p PRIME, p >> n^3, NEVER n=p-1).
  eta_b = sum_{x in mu_n} e_p(b x)              (Gauss period / period sum)
  M(n)  = max_{b != 0} |eta_b|                  (the prize sup-norm; target <= C sqrt(n log(p/n)))
  Johnson cap: list size stays trivial while M(n) <= ~ sqrt(n*S) at the Johnson radius;
               PAST Johnson needs M(n) = O(sqrt(n log(p/n))), i.e. M/sqrt(n) = O(sqrt(log(p/n))).

THE TWO FORMS OF "LARGE SIEVE" C30 COULD MEAN, both tested:

 (A) ADDITIVE large sieve over the frequency family {eta_b}_b  (Montgomery-Vaughan).
     2r-th moment  sum_b |eta_b|^{2r} = q * E_r(mu_n)  EXACTLY (additive orthogonality).
     Large-sieve bound = (M_supp + delta^{-1}) * ||f||_2^2 = (q+q) E_r = 2 q E_r >= the exact
     value. So it is *exactly saturated* (no slack) and the sup it yields is the Parseval/
     moment sup  (q E_r)^{1/2r}. Whether THAT passes Johnson is the open moment question
     E_r <= (2r-1)!! n^r.  -> we MEASURE this sup vs Johnson directly.

 (B) MULTIPLICATIVE large sieve over the GAUSS-SUM family {g(chi_s)}_{s in Z/f},  f=(p-1)/n
     (this is the Sawin-Shusterman / family-orthogonality side that C30 literally names).
     eta_b = (1/f) sum_{s=0}^{f-1} conj(chi_s)(b) g(chi_s),   chi_s = generator^{s*?} of order p-1
     The large sieve over a family of N characters has discrepancy ~ N/sqrt(q); here the
     family dimension at depth r is d_r ~ f^r/r!. Effective (discrepancy<1) IFF f <= sqrt(q),
     i.e.  (p-1)/n <= sqrt(p)  <=>  n >= sqrt(p).  The PRIZE regime is n << sqrt(p): the
     family is OVER-DIMENSIONED -> the multiplicative large sieve is VACUOUS.
     -> we MEASURE f/sqrt(p) over prize-shaped (n,p) to show f >> sqrt(p) (vacuity factor).

VERDICT LOGIC:
  - If (A)'s amplified sup only touches the *trivial/Parseval* sqrt(qn) at r=1 and needs the
    UNPROVEN moment bound E_r<=(2r-1)!!n^r to pass Johnson => SECRETLY-OPEN (the amplification
    reduces to the open BGK/energy moment, not a theorem one may invoke).
  - If (B) is vacuous (f >> sqrt(p)) in the prize regime => the named Sawin-Shusterman family-
    orthogonality machinery does not even fire there.
  Together: C30 does not pin delta* past Johnson from proven math.
"""
import cmath, math
from collections import Counter
from sympy import isprime


def find_subgroup_gen(n, p):
    """A generator z of the order-n subgroup, with z^{n/2} = -1 (faithful 2-power subgroup)."""
    for a in range(2, p):
        z = pow(a, (p - 1) // n, p)
        if pow(z, n, p) == 1 and pow(z, n // 2, p) == p - 1:
            return z
    raise RuntimeError("no faithful subgroup generator")


def mu_n(n, p):
    z = find_subgroup_gen(n, p)
    return [pow(z, j, p) for j in range(n)]


def find_prime(n, beta):
    """Smallest prime p ≡ 1 (mod n) with p ~ n^beta (so p >> n^3 for beta>=4; here we use
    moderate beta to keep the full eta-scan feasible, but ALWAYS p >> n^3 and n != p-1)."""
    target = int(round(n ** beta))
    p = target - (target % n) + 1
    while not isprime(p) or (p - 1) == n:  # forbid the full group n=p-1
        p += n
    return p


def eta_all(mu, p):
    w = 2j * math.pi / p
    return [sum(cmath.exp(w * ((b * x) % p)) for x in mu) for b in range(p)]


def sumset_indicator_r(mu, p, r):
    cur = Counter({x: 1 for x in mu})
    for _ in range(r - 1):
        nxt = Counter()
        for s, c in cur.items():
            for x in mu:
                nxt[(s + x) % p] += c
        cur = nxt
    return cur


def E_r(mu, p, r):
    return sum(c * c for c in sumset_indicator_r(mu, p, r).values())


def double_factorial_odd(r):
    """(2r-1)!! = 1*3*5*...*(2r-1)."""
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


def report(n, beta, rmax):
    p = find_prime(n, beta)
    assert p > n ** 3, f"need p>>n^3, got p={p}, n^3={n**3}"
    assert (p - 1) != n, "must be proper subgroup, never n=p-1"
    mu = mu_n(n, p)
    etas = eta_all(mu, p)
    f_idx = (p - 1) // n  # the multiplicative-family dimension f
    M_exact = max(abs(e) for b, e in enumerate(etas) if b != 0)
    sqrtn = math.sqrt(n)
    johnson_target = math.sqrt(2 * math.log(p / n))  # M/sqrt(n) must be O(sqrt(log(p/n))) past Johnson

    print(f"\n=== n={n}  p={p}  beta_eff={math.log(p)/math.log(n):.3f}  "
          f"f=(p-1)/n={f_idx}  p>n^3:{p>n**3}  proper:{(p-1)!=n} ===")
    print(f"  [B] MULTIPLICATIVE Sawin-Shusterman family dimension f={f_idx},  sqrt(p)={math.sqrt(p):.1f}")
    print(f"      f/sqrt(p) = {f_idx/math.sqrt(p):.3f}   "
          f"(effective large sieve needs f<=sqrt(p) i.e. <=1; n>=sqrt(p) is {'TRUE' if n>=math.sqrt(p) else 'FALSE -> family OVER-dimensioned, sieve VACUOUS'})")
    print(f"  M(n)/sqrt(n)         = {M_exact/sqrtn:.3f}   "
          f"Johnson-passing needs M/sqrt(n)=O(sqrt(log(p/n)))={johnson_target:.3f}")
    print(f"  [A] amplified additive large sieve sup (q*E_r)^(1/2r) vs Wick & Johnson:")
    for r in range(1, rmax + 1):
        Er = E_r(mu, p, r)
        wick = double_factorial_odd(r) * (n ** r)  # the CONJECTURED (open) energy bound
        lhs_full = sum(abs(e) ** (2 * r) for e in etas)
        parseval = p * Er
        ls_rhs = 2 * p * Er  # additive large-sieve RHS (M+delta^-1)=2q
        M_via_parseval = parseval ** (1.0 / (2 * r))
        M_via_ls = ls_rhs ** (1.0 / (2 * r))
        # If we GRANT the open moment bound E_r<=wick, the sup would be:
        M_if_wick = (p * wick) ** (1.0 / (2 * r))
        passes = "PASSES Johnson" if M_via_parseval / sqrtn <= johnson_target * 1.01 else "above Johnson"
        print(f"    r={r:2d}: E_r={Er:.3e}  Wick(2r-1)!!n^r={wick:.3e}  E_r/Wick={Er/wick:.3f}  "
              f"|qE_r - sum|eta|^2r|={abs(parseval-lhs_full):.1e}")
        print(f"           sup via Parseval/sqrtn={M_via_parseval/sqrtn:.3f}  via LargeSieve/sqrtn={M_via_ls/sqrtn:.3f}  "
              f"(if-Wick-granted/sqrtn={M_if_wick/sqrtn:.3f})  [{passes}]")


if __name__ == "__main__":
    print("ATTACK C30: Sawin-Shusterman large sieve for Gauss sums (family orthogonality).")
    print("Q1: does the AMPLIFIED additive large sieve reach the MAX past Johnson WITHOUT the open moment bound?")
    print("Q2: does the MULTIPLICATIVE (Sawin-Shusterman) family sieve even fire in the prize regime n<<sqrt(p)?")
    # proper subgroups, p prime, p>>n^3, never n=p-1. beta moderate so full eta-scan is feasible,
    # but the structural ratios (f/sqrt(p), E_r/Wick) are the load-bearing prize-regime indicators.
    for n in [8, 16]:
        for beta in [3.5, 4.0]:
            try:
                report(n, beta, rmax=2 * int(math.log2(n)))
            except Exception as ex:
                print(f"  n={n} beta={beta} ERROR {ex}")
    print("\n--- prize-shaped dimension check (structural; large p, no eta-scan) ---")
    for n in [2 ** 10, 2 ** 20, 2 ** 30]:
        for beta in [4.0, 5.0]:
            p = find_prime(n, beta) if n <= 2 ** 20 else None
            if p is None:
                # for n=2^30 just compute the asymptotic ratio at p=n^beta
                p = int(round(n ** beta))
            f_idx = (p - 1) // n
            print(f"  n=2^{int(math.log2(n))}  beta={beta}: f=(p-1)/n~{f_idx:.3e}  sqrt(p)~{math.sqrt(p):.3e}  "
                  f"f/sqrt(p)~{f_idx/math.sqrt(p):.3e}  (n>=sqrt(p)? {n>=math.sqrt(p)})  "
                  f"=> Sawin-Shusterman sieve {'EFFECTIVE' if n>=math.sqrt(p) else 'VACUOUS (over-dimensioned)'}")
    print("\nDONE")

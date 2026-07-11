#!/usr/bin/env python3
"""
probe_pinning_subset_coset_rigidity.py  (#444 — extend SinglePencilQIndependence/GeneralPencilPacking)

LANE (extends a PROVEN theorem; NON-redundant per efficiency discipline):
  The in-tree packing bound  #bad * C(a, k+1) <= C(|mu|, k+1)  (mca_badscalar_packing, axiom-clean)
  lands in the W5 SUPPLY STRIP (C(n,r)/(r+1)), NOT the prize window.  The HONEST residual flagged in
  mca_badscalar_sharp's docstring is:
     "the pinning (k+1)-subsets are COSET-STRUCTURED, not arbitrary"
  IF the pinning (k+1)-subsets that actually occur as bad-scalar witnesses are forced to be unions of
  m-power fibre cosets (the KKH26 supply shape), then the effective #bad is bounded by the COSET-
  structured (k+1)-subsets = 2^r * C(2^{mu-1}, r) (the prize budget), NOT all C(n,k+1).  That collapse
  is exactly the supply-strip -> prize-window step.  This probe MEASURES whether that rigidity holds.

THE OBJECT (matched to SinglePencilQIndependence semantics):
  - smooth 2-power domain mu_n = <g>, |mu_n| = n = 2^mu, prize prime p ~ n^beta, p == 1 mod n, PROPER.
  - the deep-band WORST-CASE far line is the KKH26 line  u0 = x^{r m}, u1 = x^{(r-1) m}, k=(r-2)m+1.
    (here m=1 => n=2^mu; the file's smooth domain.  We take m=1 for the pure 2-power prize core.)
  - for a bad scalar gamma: Q0 + gamma*Q1 = x^{rm} + gamma*x^{(r-1)m} agrees with a deg<k codeword on
    a>=k+1 points of mu_n.  the PINNING (k+1)-subset S: the unique deg<k interpolant on any (k+1)-subset
    of the agreement set IS the codeword, and S pins gamma = -(coeff structure).
  - COSET STRUCTURE: with m=1 the "m-power fibres" degenerate; the relevant rigidity for the pure
    2-power core is whether the pinning subsets are unions of cosets of the 2-power SUBGROUPS
    mu_{2^j} <= mu_n (the dyadic tower), i.e. closed under multiplication by a root of unity of 2-power
    order.  We test: is every pinning (k+1)-subset a union of cosets of mu_d for some nontrivial d|n?

MEASUREMENT (exact mod-p, PROPER subgroup, prize primes, NEVER n=q-1, multi-prime for p-independence):
  For n=2^mu (mu=3,4), r small (r=2,3 => a=k+1=r... actually agreement threshold a; we read at a=k+1):
   (1) enumerate ALL bad gamma at the binding band a (brute over gamma in F_p is too big; instead we
       enumerate over (k+1)-subsets S of mu_n, compute the pinned gamma_S from the divided-difference /
       interpolation residual, and collect the DISTINCT realized gammas + which subsets realize each).
   (2) for each distinct realized gamma, list its pinning (k+1)-subsets.  Check COSET-RIGIDITY:
       does each pinning subset equal a union of nontrivial-subgroup cosets? what fraction are
       "coset-structured" vs "generic"?
   (3) COUNT: #distinct-realized-gamma  vs  the two budgets C(n,k+1)/C(a,k+1) (packing, supply strip)
       and 2^r*C(2^{mu-1}, r) (prize).  Which does #realized track?
  THINNESS CONTROL (rule 3): repeat on a THICK subgroup (n NOT a 2-power, e.g. n=6,12) — the rigidity
  must be 2-POWER-SPECIFIC if it is the right prize mechanism (a thickness-monotone rigidity is wrong).

HONESTY: this is a STRUCTURE measurement, not a proof.  A clean "every realized pinning subset is a
2-power-coset union, and #realized = 2^r*C(2^{mu-1},r)" finding would IDENTIFY the rigidity lemma to
formalize (a real brick: it converts the packing supply-strip bound to the prize budget on the KKH26
line).  A "no, pinning subsets are generic / #realized >> prize budget" finding REFUTES the coset-
rigidity residual and pins WHY the packing route stays in the supply strip (also a result).  No Lean
changed in the probe => axiom-clean trivially.  NEVER validate on n=q-1.
"""
import itertools, sys
from collections import defaultdict

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def find_prime(n, beta_min):
    # smallest prime p == 1 mod n with p > n^beta_min
    target = n ** beta_min
    t = ((target // n) + 1) * n + 1
    while True:
        if isprime(t):
            return t
        t += n

def primitive_root_subgroup(p, n):
    # find g of multiplicative order exactly n in F_p (n | p-1)
    assert (p - 1) % n == 0
    cof = (p - 1) // n
    # find a generator h of F_p^*
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    for cand in range(2, p):
        h = pow(cand, cof, p)
        if h != 1 and order(h) == n:
            return h
    raise RuntimeError("no generator")

def inv(a, p):
    return pow(a, p-2, p)

def interp_residual_pins_gamma(S_idx, mu, k, p):
    """
    Given a (k+1)-subset S (by index into mu = list of domain points), the worst-case far line is
    u0(x)=x^{rm}, u1(x)=x^{(r-1)m}.  A bad gamma is one where u0+gamma*u1 agrees with a deg<k codeword
    on S (|S|=k+1).  The deg<k interpolant of (u0+gamma*u1) on the (k+1)-set S exists & equals it iff
    the (k+1)-th divided difference of (u0+gamma*u1) over S vanishes:
        DD_{k}[u0]  + gamma * DD_{k}[u1] = 0   (linear in gamma)
    => gamma_S = - DD_k[u0](S) / DD_k[u1](S),  provided DD_k[u1](S) != 0.
    Returns gamma_S in F_p, or None if degenerate (DD_k[u1]=0).
    """
    pts = [mu[i] for i in S_idx]   # x-coords (domain points)
    # values of u0, u1 at these points; u0=x^A, u1=x^B
    A = R_M           # = r*m  (global)
    B = (R - 1) * M   # = (r-1)*m
    u0v = [pow(x, A, p) for x in pts]
    u1v = [pow(x, B, p) for x in pts]
    # top divided difference over k+1 points = leading coeff of interpolant; vanishes iff deg < k.
    def topdd(vals):
        # Newton divided differences, return the highest (order-k) coefficient
        n_ = len(vals)
        dd = list(vals)
        for level in range(1, n_):
            new = []
            for i in range(n_ - level):
                num = (dd[i+1] - dd[i]) % p
                den = (pts[i+level] - pts[i]) % p
                new.append((num * inv(den, p)) % p)
            dd = new
        return dd[0]
    d0 = topdd(u0v)
    d1 = topdd(u1v)
    if d1 % p == 0:
        return None
    gamma = (-(d0) * inv(d1, p)) % p
    return gamma

def is_coset_union(S_set, mu, p, n):
    """
    Is the subset S (a set of domain points, = subset of mu) a union of cosets of some NONTRIVIAL
    subgroup mu_d <= mu_n (d|n, 1<d<=n)?  Return the largest such d (1 if only trivial).
    mu_n = <g>; mu_d = <g^{n/d}>.  A coset of mu_d is x*mu_d.  S is a mu_d-coset-union iff S is closed
    under multiplication by g^{n/d} (the generator of mu_d).
    """
    mu_set = set(mu)
    idx = {x:i for i,x in enumerate(mu)}  # mu[i] = g^i
    Sidx = set(idx[x] for x in S_set)
    best = 1
    # divisors d of n, d>1
    for d in range(2, n+1):
        if n % d != 0: continue
        step = n // d   # g^{step} generates mu_d
        # closed under +step (mod n) in the exponent?
        closed = all(((i + step) % n) in Sidx for i in Sidx)
        if closed:
            best = max(best, d)
    return best

def run(mu_exp_or_n, beta, r, is_two_power, label):
    global R, M, R_M
    n = (1 << mu_exp_or_n) if is_two_power else mu_exp_or_n
    R = r
    M = 1   # pure 2-power prize core: m=1, n=2^mu
    R_M = R * M
    k = (r - 2) * M + 1 if r >= 2 else 1
    a = k + 1
    if a > n:
        print(f"[{label}] n={n} r={r} k={k}: a={a} > n, skip"); return
    p = find_prime(n, beta)
    g = primitive_root_subgroup(p, n)
    mu = [pow(g, i, p) for i in range(n)]   # mu[i] = g^i
    print(f"[{label}] n={n} (2^?={is_two_power}) r={r} k={k} a={a} p={p} (p~n^{beta}, p mod n={p%n}) m={M}")
    # enumerate all (k+1)=a-subsets, pin gamma_S
    gamma_to_subsets = defaultdict(list)
    degen = 0
    total = 0
    for S_idx in itertools.combinations(range(n), a):
        total += 1
        gS = interp_residual_pins_gamma(S_idx, mu, k, p)
        if gS is None:
            degen += 1; continue
        gamma_to_subsets[gS].append(S_idx)
    realized = len(gamma_to_subsets)
    # budgets
    from math import comb
    packing_strip = comb(n, k+1) // comb(a, k+1)   # C(n,k+1)/C(a,k+1) ; a=k+1 => C(a,k+1)=1
    half = n // 2 if is_two_power else None
    prize_budget = (2**r) * comb(half, r) if (is_two_power and half is not None and r <= half) else None
    # coset rigidity of pinning subsets
    coset_struct = 0
    generic = 0
    sample_generic = []
    for gS, subs in gamma_to_subsets.items():
        for S_idx in subs:
            S_set = set(mu[i] for i in S_idx)
            d = is_coset_union(S_set, mu, p, n)
            if d > 1:
                coset_struct += 1
            else:
                generic += 1
                if len(sample_generic) < 3:
                    sample_generic.append(sorted(S_idx))
    npin = coset_struct + generic
    print(f"   total a-subsets={total} degenerate(DD1=0)={degen} -> realized-distinct-gamma={realized}")
    print(f"   BUDGETS: packing-strip C(n,k+1)/C(a,k+1)={packing_strip}  prize 2^r*C(n/2,r)={prize_budget}")
    print(f"   PINNING-SUBSET coset-rigidity: coset-structured={coset_struct}/{npin}  generic={generic}/{npin}")
    if sample_generic:
        print(f"   sample generic pinning subsets (exp-indices): {sample_generic}")
    # verdict line
    if prize_budget is not None:
        ratio = realized / prize_budget if prize_budget else float('inf')
        print(f"   #realized / prize_budget = {realized}/{prize_budget} = {ratio:.3f}")
    print()

if __name__ == "__main__":
    print("=== PINNING-SUBSET COSET-RIGIDITY PROBE (extends mca_badscalar packing -> prize collapse) ===\n")
    print("--- 2-POWER prize core (n=2^mu, m=1) ---")
    for mu_exp in (3, 4):
        for r in (2, 3):
            try:
                run(mu_exp, 4, r, True, f"2pow mu={mu_exp}")
            except Exception as e:
                print(f"  [2pow mu={mu_exp} r={r}] ERROR {e}\n")
    print("--- THICK control (n NOT a 2-power; rigidity must be 2-power-specific) ---")
    for n in (6, 12):
        for r in (2, 3):
            try:
                run(n, 4, r, False, f"thick n={n}")
            except Exception as e:
                print(f"  [thick n={n} r={r}] ERROR {e}\n")

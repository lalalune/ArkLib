#!/usr/bin/env python3
"""
LANE R4a (#407), TASK 3: Does the CONSTANT-INDEX structure (m=(p-1)/n const, n->infty)
give Rojas-Leon extra automorphisms that LOWER the effective threshold below n=sqrt(p)?

Two completely different "index" notions are in play; we must not conflate them.
  - Rojas-Leon's e = index of the homothety subgroup Gamma_e in F_q^*.  Gamma_e = mu_n,
    so e = (p-1)/n.  In the prize, n -> infty and p=n^beta, so e = (p-1)/n ~ n^{beta-1}
    is LARGE and GROWING, NOT constant.
  - The prize's "constant index m": the #407 framing fixes ε* = 2^-128 and writes the
    index m = (p-1)/n.  But the actual prize sweep takes p ~ n^4..n^5, so m=(p-1)/n
    GROWS like n^3..n^4.  The "m=2^128 constant" statement in the KB refers to a
    DIFFERENT normalization (n=2^30 fixed, the security parameter), NOT the asymptotic
    n->infty sweep.  For the ANALYTIC sup-norm M(n) <= C sqrt(n log(p/n)) we need
    n->infty with p/n -> infty, i.e. e=(p-1)/n -> infty.

So the homothety group mu_n has order n (the thing we want large) and its index e in
F_p^* is e=(p-1)/n (large).  The "automorphism group G" Rojas-Leon exploits is the
homothety group itself, of order |mu_n| = n.  The hoped gain is sqrt(#G)=sqrt(n).
THAT IS EXACTLY THE PRIZE: improve the trivial bound by sqrt(n).  Let's see why his
mechanism delivers sqrt(q)=sqrt(p) gain over WEIL, but Weil here is ~ e sqrt(p) /? ...

CAREFUL recount of the scales for the bare subgroup sum (g linear, the prize case):
  S_b = sum_{x in mu_n} e_p(b x).
  Completed: S_b = (1/e) sum_{j} chi_j-bar(b) tau_j, tau_j Gauss sums, |tau_j|=sqrt(p),
  e = (p-1)/n characters trivial on mu_n.  Trivial completion bound: (1/e)*e*sqrt(p)=
  sqrt(p).  The HOMOTHETY/automorphism group acting is mu_n (order n).  Under its
  action the cohomology splits into e=(p-1)/n eigenspaces, ONE PER character chi_j.
  Each eigenspace contributes a single Gauss sum tau_j of weight 1 (modulus sqrt(p)).
  RANK = e (one per nontrivial relevant character).  There is NO eigenspace with
  MORE than weight 1; the 'gain' Rojas-Leon gets (sqrt(q) over Weil) comes from the
  rank being e rather than (degree)*e, NOT from sub-sqrt(p) per-eigenspace cancellation.

  ==> The homothety decomposition gives  |S_b| <= (1/e) * e * sqrt(p) = sqrt(p),
  i.e. EXACTLY the completion bound.  It does NOT beat sqrt(p).  To beat sqrt(p) and
  reach sqrt(n) one needs CANCELLATION AMONG THE e GAUSS SUMS tau_j -- precisely the
  joint-equidistribution / non-conspiracy that Katz-Rojas-Leon prove as q->infty, the
  EFFECTIVE form of which is the prize.  Rojas-Leon 1010.0120 does NOT provide that
  cancellation; it provides the rank count.

We now VERIFY numerically on real primes that:
  (a) M(n) ~ sqrt(p) is the homothety/completion ceiling (NOT achieved -- it's an
      upper bound; the truth is much smaller), and the e Gauss sums DO largely cancel
      (so the truth is ~ sqrt(n)-ish), confirming the gain is in the WEIGHTS/phases
      (joint equidistribution), exactly what RL does NOT give.
  (b) The number of automorphisms = |mu_n| = n does NOT change with how we choose the
      'constant index' framing; the threshold is governed by e=(p-1)/n vs sqrt(p).
"""
import cmath, math, random

def primitive_root(p):
    # find a generator of F_p^*
    if p == 2: return 1
    phi = p-1
    facs = set()
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            facs.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    return None

def mu_n_subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of the order-n subgroup
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x*h) % p
    return S

def Mn(p, n):
    S = mu_n_subgroup(p, n)
    w = 2j*math.pi/p
    best = 0.0
    for b in range(1, p):
        s = sum(cmath.exp(w*((b*x) % p)) for x in S)
        a = abs(s)
        if a > best: best = a
    return best

print("="*84)
print("TASK 3: constant-index extra-automorphism check on REAL prime fields")
print("="*84)
print("M(n)=max_{b!=0}|sum_{mu_n} e_p(bx)|. Compare to sqrt(p) (homothety ceiling) and")
print("sqrt(n) (prize scale). If M(n) << sqrt(p), the e Gauss sums CANCEL -> the gain is")
print("in the PHASES (joint equidist = Katz/RL q->infty), which Rojas-Leon 1010.0120")
print("does NOT make effective.  m=index, automorphisms=|mu_n|=n.")
print()
# primes p with n | p-1, with p ~ n^beta for various beta, small enough to brute force
cases = []
# (n, list of primes near n^beta for beta around 2..4 where feasible)
def first_prime_with_n(n, target):
    # smallest prime p >= target with n | (p-1)
    # p = 1 + k*n
    k = max(1, (target-1)//n)
    while True:
        p = 1 + k*n
        if p >= target and is_prime(p):
            return p
        k += 1

def is_prime(p):
    if p < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if p % q == 0: return p == q
    d = p-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a>=p: continue
        x = pow(a,d,p);
        if x in (1,p-1): continue
        ok=False
        for _ in range(r-1):
            x=x*x%p
            if x==p-1: ok=True;break
        if not ok: return False
    return True

print(f"{'n':>5} {'beta~':>6} {'p':>10} {'M(n)':>10} {'sqrt(p)':>10} {'sqrt(n)':>10} {'M/sqrtp':>8} {'M/sqrtn':>8}")
for n in [8, 16, 32, 64]:
    for beta in [2.0, 3.0, 4.0]:
        target = int(n**beta)
        if target > 4_000_000:   # brute-force cap
            continue
        p = first_prime_with_n(n, target)
        if p > 4_000_000:
            continue
        m = Mn(p, n)
        bet_eff = math.log(p)/math.log(n)
        print(f"{n:>5} {bet_eff:>6.2f} {p:>10} {m:>10.3f} {math.sqrt(p):>10.2f} "
              f"{math.sqrt(n):>10.3f} {m/math.sqrt(p):>8.4f} {m/math.sqrt(n):>8.3f}")
print()
print("READING: M(n)/sqrt(p) -> 0 (the e Gauss sums cancel heavily) while M(n)/sqrt(n)")
print("stays O(1)-ish -> the truth is ~ sqrt(n), the prize. The homothety mechanism's")
print("ceiling sqrt(p) is FAR above. The gain to sqrt(n) is pure phase-cancellation")
print("among the e Gauss sums = joint equidistribution (Katz/RL ASYMPTOTIC), which the")
print("EFFECTIVE Rojas-Leon 1010.0120 does NOT deliver at fixed p. NO extra automorphism")
print("from 'constant index' -- automorphism count is |mu_n|=n either way; threshold is")
print("e=(p-1)/n vs sqrt(p), i.e. n vs sqrt(p), unchanged.")

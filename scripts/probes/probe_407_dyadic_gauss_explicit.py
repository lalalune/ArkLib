#!/usr/bin/env python3
"""
ATTACK 1 (#407) — DYADIC GAUSS-PHASE EXPLICIT EVALUATION.

Claim under test (system prompt): "For dyadic mu_n the relevant chi have 2-POWER order,
classically evaluable; does the explicit dyadic evaluation bound max|P| WITHOUT the
generic flatness conjecture?"

EXACT IDENTITY (corrected, verified 1e-13 in probe_407_gauss_phase_identity_corrected.py):
   eta_b = sum_{y in mu_n} e_p(b y) = (1/m)[ -1 + sum_{a != 0, a ≡ 0 mod n} chibar_a(b) G(chi_a) ]
   m = (p-1)/n.  The relevant characters are those TRIVIAL ON mu_n: chi_a with a ≡ 0 mod n,
   i.e. a = n*j, j = 0..m-1.  These are the m characters of the quotient F_p^* / mu_n ≅ Z/m.
   With gamma_a = G(chi_a)/sqrt(p) (unimodular, |G|=sqrt p), eta_b = (-1 + sqrt(p) P(b))/m,
   P(b) = sum_{j=1}^{m-1} chibar_{nj}(b) gamma_{nj}.

THE STRUCTURAL POINT (this probe's first verdict):
   The order of chi_{nj} is (p-1)/gcd(nj, p-1) = m/gcd(j, m).  As j ranges over Z/m, the orders
   that appear are exactly the divisors of m.  So the relevant characters have order dividing m,
   NOT order dividing n.  The "2-power order" claim is TRUE iff m = (p-1)/n is a 2-power.
   For a 2-power n, m a 2-power means p-1 = n*m is a 2-power => p is a Fermat prime
   (p = 2^k + 1).  Generic dyadic primes have m with large odd part => the gamma_a are
   Gauss sums of LARGE (non-2-power) order, NOT classically evaluable.

So the "dyadic special node" as stated is a CORNER (Fermat primes), not the generic dyadic regime.

This probe:
 (1) Confirms which character orders actually appear in P(b), per (p,n).
 (2) On the genuine 2-power-everything corner (Fermat primes: p=17,257,65537; m and n both 2-powers),
     computes the EXPLICIT classical Gauss phases (quadratic / quartic via p=a^2+b^2 / octic via
     Jacobi sums) and verifies them against direct G(chi)/sqrt(p), then asks whether the explicit
     structure bounds max|P| <= sqrt(2 m ln m) WITHOUT a flatness conjecture.
 (3) Tests the Jacobi cocycle gamma_a gamma_b = (J/sqrt p) gamma_{a+b} and whether it makes P
     a structured (geometric/telescoping) sum that is bounded below the generic flat value.
"""
import cmath, math
from collections import Counter

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; facs = set(); x = phi; d = 2
    while d*d <= x:
        while x % d == 0: facs.add(d); x //= d
        d += 1
    if x > 1: facs.add(x)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs): return g
    raise RuntimeError

def order_of(a, m):
    # order of element a in Z/m under +  is m/gcd(a,m); but order of CHARACTER chi_a is (p-1)/gcd(a,p-1)
    pass

# ---------------------------------------------------------------------------
# Part (1): which character orders appear in P(b)?
# ---------------------------------------------------------------------------
def char_orders(p, n):
    phi = p-1; m = phi//n
    orders = Counter()
    for j in range(1, m):           # a = n*j, j=1..m-1 (drop a=0 trivial)
        a = n*j
        ordr = phi // math.gcd(a, phi)
        orders[ordr] += 1
    return m, orders

print("="*100)
print("PART 1: orders of the characters appearing in P(b) (a ≡ 0 mod n, a != 0).")
print("The system-prompt 'dyadic special' assumes these are all 2-power order.")
print("="*100)
print(f"{'p':>7} {'n':>4} {'m=(p-1)/n':>10} {'m_odd_part':>11} {'all 2-power order?':>20}  order multiset")
cases = [(13,3),(41,8),(97,8),(257,16),(241,8),(337,16),
         (17,8),(17,16),(257,256),(65537,256),(65537,1024),(673,32),(769,256),(12289,2048)]
for p, n in cases:
    if (p-1) % n: continue
    m, orders = char_orders(p, n)
    odd = m
    while odd % 2 == 0: odd //= 2
    all_two_power = all((o & (o-1)) == 0 for o in orders)   # power of two (incl 1)
    omult = ", ".join(f"{o}×{c}" for o, c in sorted(orders.items()))
    print(f"{p:>7} {n:>4} {m:>10} {odd:>11} {str(all_two_power):>20}  {omult}")

print()
print("VERDICT(1): the relevant characters have order dividing m=(p-1)/n, NOT dividing n.")
print("They are all 2-power order IFF m is a 2-power IFF p-1 = n*m is a 2-power IFF p is a Fermat prime.")
print()

# ---------------------------------------------------------------------------
# Part (2): EXPLICIT classical evaluation on the genuine 2-power corner (Fermat primes).
# ---------------------------------------------------------------------------
def dlog_table(p, g):
    d = {}; val = 1
    for k in range(p-1):
        d[val] = k; val = val*g % p
    return d

def gauss_sum(p, g, dlog, a):
    # G(chi_a) = sum_{x != 0} chi_a(x) e_p(x), chi_a(g^k) = exp(2 pi i a k/(p-1))
    phi = p-1
    return sum(cmath.exp(2j*math.pi*a*dlog[x]/phi) * cmath.exp(2j*math.pi*x/p) for x in range(1, p))

def jacobi_sum(p, g, dlog, a, b):
    # J(chi_a, chi_b) = sum_{x} chi_a(x) chi_b(1-x),  x in F_p \ {0,1}
    phi = p-1
    s = 0
    for x in range(2, p):          # x != 0, x != 1
        y = (1 - x) % p
        if y == 0: continue
        s += cmath.exp(2j*math.pi*a*dlog[x]/phi) * cmath.exp(2j*math.pi*b*dlog[y]/phi)
    return s

print("="*100)
print("PART 2: EXPLICIT classical Gauss-phase evaluation on FERMAT-prime corner (m, n both 2-powers).")
print("Verify gamma_a = G(chi_a)/sqrt(p) against the classical closed forms; verify Jacobi cocycle.")
print("="*100)

# Fermat-prime cases where BOTH m and n are 2-powers (so ALL relevant chars are 2-power order):
# (Jacobi sum is O(p) per pair, O(m^2) pairs => keep m moderate; 65537 with m=256 is the stretch.)
fermat_cases = [(17,8),(17,16),(257,16),(257,128),(65537,512),(65537,256)]
for p, n in fermat_cases:
    if (p-1) % n: continue
    g = primitive_root(p); phi = p-1; m = phi//n
    dlog = dlog_table(p, g)
    a_list = [n*j for j in range(m)]           # j=0..m-1
    # |G(chi_a)| = sqrt p for a != 0:
    gabs = [abs(gauss_sum(p, g, dlog, a)) for a in a_list if a != 0]
    maxdev = max(abs(x - math.sqrt(p)) for x in gabs) if gabs else 0.0

    # Jacobi cocycle: G(chi_a) G(chi_b) = J(chi_a,chi_b) G(chi_{a+b})  when chi_a chi_b != 1.
    # We DEFINE J via the cocycle J(a,b) = G(a)G(b)/G(a+b) (exact since G != 0), then verify
    # |J| = sqrt p (the classical Jacobi magnitude) directly — a few O(p) direct J checks confirm
    # the definition agrees with sum_x chi_a(x) chi_b(1-x).  This avoids O(m^2) O(p) sums.
    Gcache = {a: gauss_sum(p, g, dlog, a) for a in a_list}
    jabs = []
    for ia in range(1, m):
        for ib in range(1, m):
            a, b = n*ia, n*ib
            ab = (a+b) % phi
            if ab == 0: continue                # chi_a chi_b = 1, separate (G(chi)G(chibar)=chi(-1)p)
            Jcoc = Gcache[a]*Gcache[b]/Gcache[ab]
            jabs.append(abs(Jcoc))
    jdev = max(abs(x - math.sqrt(p)) for x in jabs) if jabs else 0.0
    # spot-check the cocycle definition equals the direct Jacobi sum on a few pairs:
    cocyc_err = 0.0
    spot = [(n*1, n*1), (n*1, n*2), (n*2, n*3)]
    for a, b in spot:
        if a >= phi or b >= phi: continue
        ab = (a+b) % phi
        if ab == 0: continue
        Jdir = jacobi_sum(p, g, dlog, a, b)
        Jcoc = Gcache[a]*Gcache[b]/Gcache[ab]
        cocyc_err = max(cocyc_err, abs(Jdir - Jcoc))

    # max|P(b)|:
    def chibar(a, b):
        return 0 if b % p == 0 else cmath.exp(-2j*math.pi*a*dlog[b % p]/phi)
    maxP = 0.0
    for b in range(1, p):
        Pb = sum(chibar(a, b)*(Gcache[a]/math.sqrt(p)) for a in a_list if a != 0)
        maxP = max(maxP, abs(Pb))
    budP = math.sqrt(2*m*math.log(m)) if m > 1 else 1.0
    print(f"p={p:>6} n={n:>4} m={m:>4} | ||G|-√p|={maxdev:.1e} |J|cocycle_err={cocyc_err:.1e} "
          f"||J|-√p|={jdev:.1e} | max|P|={maxP:.3f} √(2m·lnm)={budP:.3f} ratio={maxP/budP:.3f}")

print()
print("VERDICT(2): on the Fermat corner, |G|=|J|=√p EXACTLY and the Jacobi cocycle holds exactly,")
print("so gamma_a are explicit unimodular algebraic numbers. BUT the cocycle |J|/√p = 1 (unimodular)")
print("means gamma_a gamma_b = (unit) gamma_{a+b}: the phases COMBINE WITHOUT CONTRACTION.")
print("P(b) = sum of m-1 UNIT phases (no geometric decay) — the explicit structure gives NO")
print("a-priori sub-flat bound; max|P| ~ flat value sqrt(2 m ln m). See Part 3.")

# ---------------------------------------------------------------------------
# Part (3): why the Jacobi cocycle CANNOT contract P below the flat budget.
# ---------------------------------------------------------------------------
print()
print("="*100)
print("PART 3: the cocycle is non-contractive => no explicit sub-flat bound. Two telescopes.")
print("="*100)
print("""
Write gamma_j := gamma_{n j} = G(chi_{nj})/sqrt(p), j in Z/m (gamma_0 = G(triv)/sqrt p = -1/sqrt p,
but we drop j=0).  The Hasse-Davenport / Jacobi cocycle gives, for j,k with j+k != 0 (mod m):

      gamma_j * gamma_k = (J_{j,k}/sqrt p) * gamma_{j+k},    |J_{j,k}| = sqrt p  (EXACT, Part 2).

So the *normalized cocycle*  c_{j,k} := J_{j,k}/sqrt p  is UNIMODULAR (|c|=1).  Consequences:

(i) TELESCOPE: gamma_j = gamma_1^{(j)} := (prod of unit cocycles) * gamma_1^j-ish — more precisely
    gamma_j = u_j * gamma_1^j / sqrt p^{j-1} ... NO: since each step multiplies by a UNIT and
    divides nothing, |gamma_j| = 1 for all j (consistent: |G|=sqrt p).  The phases are
    theta_j = arg(gamma_j); the cocycle says theta_{j+k} = theta_j + theta_k - arg(c_{j,k}),
    i.e. theta is a quasi-morphism with unimodular coboundary.  There is NO decay term.

(ii) P(b) = sum_{j=1}^{m-1} chibar_{nj}(b) gamma_j = sum_j exp(i(phi_j(b))) where each summand is a
     UNIT vector.  A bound max|P| <= sqrt(2 m ln m) is a CANCELLATION (flatness) statement about
     m-1 unit vectors; the cocycle relates their PRODUCTS, not their SUM, and being unimodular it
     transfers no smallness.  Contraction would require |c_{j,k}| < 1 (i.e. |J| < sqrt p), which
     holds ONLY for the PRINCIPAL pair (j+k = 0: G(chi)G(chibar) = chi(-1) p, "J" effectively sqrt p
     still) — never for the non-principal characters that make up P.

Numeric confirmation that P is a *flat* sum of units (no hidden geometric structure): compare
max|P| to (a) the flat conjecture sqrt(2 m ln m), and (b) a random-unimodular-sum model
E[max] ~ sqrt(m ln m): the ratio should hug ~1, NOT decay.
""")

import random
def primitive_root2(p): return primitive_root(p)
print(f"{'p':>7} {'n':>5} {'m':>5} {'max|P|':>8} {'√(2m·lnm)':>10} {'ratio':>6} {'√(m·lnm)':>9} {'L2=√(m-1)':>10}")
for p, n in [(41,8),(97,8),(241,8),(337,16),(257,16),(673,32),(769,256),(12289,2048)]:
    if (p-1) % n: continue
    g = primitive_root(p); phi = p-1; m = phi//n
    dlog = dlog_table(p, g)
    a_list = [n*j for j in range(1, m)]
    Gn = {a: gauss_sum(p, g, dlog, a)/math.sqrt(p) for a in a_list}
    def chibar(a, b): return 0 if b % p == 0 else cmath.exp(-2j*math.pi*a*dlog[b % p]/phi)
    maxP = 0.0
    for b in range(1, p):
        Pb = sum(chibar(a, b)*Gn[a] for a in a_list)
        maxP = max(maxP, abs(Pb))
    bud = math.sqrt(2*m*math.log(m)) if m > 1 else 1.0
    l2 = math.sqrt(max(m-1, 0))                 # Parseval: sum_b|P(b)|^2 = (m-1)(something); rough L2 scale
    rms = math.sqrt(m*math.log(m)) if m > 1 else 1.0
    print(f"{p:>7} {n:>5} {m:>5} {maxP:>8.3f} {bud:>10.3f} {maxP/bud:>6.3f} {rms:>9.3f} {l2:>10.3f}")

print()
print("OVERALL VERDICT — ATTACK 1: NO. The explicit dyadic Gauss-phase evaluation does NOT bound")
print("max|P| below the generic flatness conjecture, for TWO independent reasons:")
print(" (R1) STRUCTURAL: the characters in P(b) are trivial-on-mu_n, dual group Z/m, m=(p-1)/n.")
print("      They are 2-power-order only on Fermat primes (m a 2-power). The prize regime")
print("      n=2^30, q ≈ n·2^128 has m=(p-1)/n with huge ODD part => NON-2-power Gauss sums,")
print("      NOT classically evaluable. The 'dyadic special node' is a Fermat-prime CORNER.")
print(" (R2) NON-CONTRACTIVE: even on the Fermat corner, |J|=sqrt p EXACTLY => the Jacobi cocycle")
print("      gamma_j gamma_k = (unit) gamma_{j+k} is unimodular, transfers no smallness; P is a")
print("      flat sum of m-1 unit phases and max|P|/sqrt(2m ln m) hugs 0.98-1.10 (>1 at 65537/512),")
print("      i.e. the explicit structure REPRODUCES the flat conjecture, never beats it.")
print(" => Attack 1 collapses onto WALL: BGK/Paley flatness (max|P| <= sqrt(2m ln m)) over Z/m,")
print("    the same open sup-norm wall. This is the explicit-evaluation refutation of the corner.")

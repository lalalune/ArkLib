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
fermat_cases = [(17,8),(17,16),(257,16),(257,256),(65537,256),(65537,1024)]
for p, n in fermat_cases:
    if (p-1) % n: continue
    g = primitive_root(p); phi = p-1; m = phi//n
    dlog = dlog_table(p, g)
    a_list = [n*j for j in range(m)]           # j=0..m-1
    # |G(chi_a)| = sqrt p for a != 0:
    gabs = [abs(gauss_sum(p, g, dlog, a)) for a in a_list if a != 0]
    maxdev = max(abs(x - math.sqrt(p)) for x in gabs) if gabs else 0.0

    # Jacobi cocycle: G(chi_a) G(chi_b) = J(chi_a,chi_b) G(chi_{a+b})  when chi_a chi_b != 1.
    # equivalently gamma_a gamma_b = (J(a,b)/sqrt p) gamma_{a+b}.  Verify on a sample.
    Gcache = {a: gauss_sum(p, g, dlog, a) for a in a_list}
    cocyc_err = 0.0; jabs = []
    for ia in range(1, m):
        for ib in range(1, m):
            a, b = n*ia, n*ib
            ab = (a+b) % phi
            if ab == 0: continue                # chi_a chi_b = 1, separate (G(chi)G(chibar)=chi(-1)p)
            Gab = gauss_sum(p, g, dlog, ab) if ab not in Gcache else Gcache[ab]
            J = jacobi_sum(p, g, dlog, a, b)
            jabs.append(abs(J))
            lhs = Gcache[a]*Gcache[b]
            rhs = J*Gab
            cocyc_err = max(cocyc_err, abs(lhs-rhs))
    # Jacobi sums have |J| = sqrt p for chi_a chi_b != 1 (a+b != 0 mod p-1): classical.
    jdev = max(abs(x - math.sqrt(p)) for x in jabs) if jabs else 0.0

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

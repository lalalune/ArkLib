#!/usr/bin/env python3
"""
LANE J1 (#444): Subspace theorem / S-unit / Evertse roots-of-unity COUNT bound
applied to the DIRECT sup M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|.

EXACT integer arithmetic (no float-FFT). Screens three things:

(A) Evertse 1999 bound: # non-degenerate solutions of a fixed linear relation
    a_1 z_1 + ... + a_k z_k = 0 in roots of unity is <= (k)^{3 k^2} (homogeneous
    form, k = relation length), depending ONLY on k. Compare to the actual
    char-0 Lam-Leung count of vanishing relations at the depths the prize needs.

(B) Is the COUNT bound non-vacuous at prize scale?  The relation lengths that
    matter for the sup at depth r are k = 2r with r ~ log p ~ 172. Evaluate
    (k)^{3k^2} vs the trivial total count and vs the BGK wall.

(C) The decisive char-0 vs char-p gap (Lam-Leung finite-field, 1996): in char p
    the weight set GAINS p (p*1 = 0) and -- crucially in the prize regime where
    p = 1 mod n so Phi_n splits COMPLETELY mod p -- extra SHORT genuinely-char-p
    relations appear that Evertse's char-0 theorem provably does NOT count.
    We exhibit, by exact enumeration at small prize-shaped (n,p), the shortest
    genuinely-char-p vanishing relation among n-th roots and compare its length
    to (i) the char-0 minimum (= 2, antipodal) and (ii) p.

Verdict feeds StructuredOutput.
"""
import itertools, math
from math import comb, log, isqrt
from sympy import isprime, nextprime

def double_factorial_odd(r):
    # (2r-1)!! = product of odd numbers up to 2r-1
    v = 1
    for k in range(1, 2*r, 2):
        v *= k
    return v

def evertse_bound(k):
    # homogeneous form: k^{3 k^2}  (Evertse 1999, Thm; for the inhomogeneous
    # a_1 z_1+...+a_n z_n = 1 it is (n+1)^{3(n+1)^2}, same shape with k=n+1).
    # returns log10 to avoid overflow
    return 3 * k * k * math.log10(k)

# ---------------------------------------------------------------------------
print("="*78)
print("(A)/(B): Evertse count bound vs char-0 Lam-Leung count vs trivial total")
print("="*78)
print(f"{'r':>4} {'k=2r':>5} {'log10 Evertse k^{3k^2}':>22} {'log10 (2r-1)!! n^r (Wick, n=2^30)':>34}")
mu = 30; n = 1 << mu          # prize scale n = 2^30
for r in [1,2,3,5,10,50,100,172]:
    k = 2*r
    ev = evertse_bound(k) if k >= 2 else 0.0
    wick = math.log10(double_factorial_odd(r)) + r*math.log10(n)
    print(f"{r:>4} {k:>5} {ev:>22.1f} {wick:>34.1f}")

print()
print("Interpretation:")
print(" - Evertse counts NON-DEGENERATE solutions of a FIXED-coefficient relation,")
print("   bound depends ONLY on k=relation length, NOT on field/order/p.")
print(" - The energy E_r counts ALL (degenerate-allowed) coincidences over mu_n^{2r};")
print("   its char-0 value is (2r-1)!! n^r (Lam-Leung antipodal matchings).")
print(" - These are DIFFERENT objects: Evertse bounds the number of DISTINCT relation")
print("   TYPES (up to proportionality); the energy multiplies by n^r free placements.")

# ---------------------------------------------------------------------------
print()
print("="*78)
print("(C) char-0 vs char-p shortest genuine relation, exact, prize-SHAPED (n,p)")
print("    p = 1 mod n  => Phi_n splits completely mod p (prize condition).")
print("    Question: shortest nonzero +-sum of n-th roots that is 0 mod p but !=0 over Z[zeta].")
print("="*78)

def first_prime_1_mod_n_at_least(n, lo):
    p = nextprime(lo-1)
    while True:
        if (p - 1) % n == 0:
            return p
        p = nextprime(p)

def shortest_charp_relation(n, p, max_len=8):
    """
    mu_n = {h^j} for h a primitive n-th root in F_p.  We look for the shortest
    SIGNED subset relation sum eps_i h^{a_i} = 0 in F_p with NOT all-zero over Z
    (i.e. genuinely char-p), among DISTINCT exponents (so it is a real short
    relation, not a multiset reusing antipodes). Returns (len, witness) or None.
    char-0 antipodal relation h^a + h^{a+n/2} = 0 is ALWAYS char-0 (zero over Z[zeta]),
    so we EXCLUDE relations that are unions of antipodal pairs.
    """
    # primitive n-th root in F_p
    g = 2
    while pow(g, (p-1)//n, p) == 1 and n>1:
        # need element of exact order n: take generator^((p-1)/n)
        break
    # robust: find generator of F_p^*
    def order(a):
        o=1; x=a%p
        while x!=1:
            x=(x*a)%p; o+=1
        return o
    # find primitive root
    pr=2
    while order(pr)!=p-1:
        pr+=1
    h = pow(pr, (p-1)//n, p)  # exact order n
    powers = [pow(h, j, p) for j in range(n)]
    half = n//2
    # candidate short relations: choose subset S of size L of exponents, signs eps in {+1,-1}
    # check sum == 0 mod p; exclude pure antipodal (char-0).
    best=None
    for L in range(2, max_len+1):
        for combo in itertools.combinations(range(n), L):
            # try all sign patterns; fix first sign +1 by symmetry
            for signs in itertools.product([1,-1], repeat=L-1):
                eps=[1]+list(signs)
                s=0
                for e,a in zip(eps,combo):
                    s=(s+e*powers[a])%p
                if s==0:
                    # check whether genuinely char-0 zero:
                    # it's char-0 zero iff multiset of (signed) roots cancels over Z[zeta_n]
                    # for distinct exponents with +-1, char-0 zero requires antipodal pairing:
                    # i.e. the set partitions into pairs {a, a+half} with opposite signs (or same? -h^a+h^a impossible distinct)
                    # Pure antipodal char-0: h^a - h^a? no (distinct). h^a + h^{a+half}=0 needs eps equal.
                    char0 = is_char0_zero(combo, eps, half, n)
                    if not char0:
                        return (L, list(zip(eps,combo)))
        if best: break
    return None

def is_char0_zero(combo, eps, half, n):
    """Is sum eps_i zeta^{a_i} = 0 already over Z[zeta_n]?
    For 2-power n, by Lam-Leung the only vanishing relations are generated by
    antipodal pairs zeta^a + zeta^{a+n/2} = 0. So char-0 zero iff the signed
    multiset partitions into such pairs (a with +, a+half with + give zeta^a+zeta^{a+half}=0)."""
    items = list(zip(combo, eps))
    used=[False]*len(items)
    for i in range(len(items)):
        if used[i]: continue
        ai,ei=items[i]
        # need partner (ai+half) mod n with SAME sign (since zeta^a + zeta^{a+half}=0)
        found=False
        for j in range(len(items)):
            if used[j] or j==i: continue
            aj,ej=items[j]
            if (ai+half)%n==aj%n and ei==ej:
                used[i]=used[j]=True; found=True; break
        if not found:
            return False
    return all(used)

for mu_s in [3,4,5]:          # n=8,16,32 (exact-enumerable)
    n = 1<<mu_s
    # prize-shaped: smallest p = 1 mod n with p >= n^4 (beta=4)
    p = first_prime_1_mod_n_at_least(n, n**4)
    res = shortest_charp_relation(n, p, max_len=6)
    if res:
        L,wit = res
        print(f"n={n:>4}  p={p:>12} (~n^4)   shortest GENUINE char-p relation length = {L}")
        print(f"         char-0 minimum length = 2 (antipodal).  p = {p}.  L vs p: {L} << {p}")
    else:
        print(f"n={n:>4}  p={p:>12}   no genuine char-p relation up to length 6 (norm-protected at this n)")

print()
print("VERDICT logic:")
print(" * Evertse/Schlickewei/ESS bound is a CHAR-0 theorem (Evertse states: works")
print("   for any field of CHARACTERISTIC ZERO). It counts non-degenerate relation")
print("   types, = the Lam-Leung antipodal structure = the (2r-1)!! Wick count.")
print(" * The prize gap is the CHAR-p excess W_r = genuine char-p relations (sum=0")
print("   mod p, nonzero over Z[zeta]). Lam-Leung-finite-field: in char p the weight")
print("   set GAINS short relations (p*1=0; and splits-completely adds more). These")
print("   are EXACTLY the relations Evertse's char-0 count does NOT see.")
print(" * If a genuine char-p relation of length L << p exists at prize-shaped (n,p),")
print("   the char-0 count provides ZERO upper bound on them => VACUOUS for the gap.")

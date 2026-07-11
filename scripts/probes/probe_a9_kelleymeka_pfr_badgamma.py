"""
A9 [Kelley-Meka / PFR] probe: does post-2023 additive-structure theory cap the
bad-gamma / vanishing-subset locus BELOW the budget n, PAST Johnson?

The new-lemma candidate (manifesto angle 9):
  CLAIM: the bad-gamma locus B(a,b,delta) = {gamma in F_p : x^a + gamma x^b is delta-close
  to RS[mu_n,k]} is a 3-term-progression-like / vanishing-subset additive object whose size
  the now-PROVEN PFR theorem (GGMT 2023) + Kelley-Meka exp-improved Roth (2023) force into
  <= n cosets of a bounded-index subgroup, PAST the Johnson radius.

This probe is the ADVERSARIAL test of every hypothesis KM/PFR would need to be NON-vacuous,
computed exactly over PROPER subgroups mu_n (p PRIME, n=2^mu, n | p-1, p >> n^3, NEVER n=p-1).

KM theorem (2023): A subset of F_p of density alpha with NO nontrivial 3AP has
  alpha <= exp(-c (log p)^{1/12}).  [It ONLY constrains 3AP-FREE sets.]
PFR theorem (2023): A set A with additive doubling K=|A+A|/|A| is covered by
  <= K^C cosets of a subgroup H with |H| <= |A|.  [Vacuous once K^C >= |A|.]

We test, for the bad-gamma SET as an additive object in F_p:
  (T1) its additive density alpha = |B|/p   (vs the KM 3AP ceiling ~ 1/(log p)^{1+c})
  (T2) is B 3AP-FREE? (KM only bites 3AP-free sets) -> count 3APs inside B
  (T3) its additive doubling K = |B+B|/|B|     (PFR is vacuous when K^C >= |B|)
  (T4) how many additive-subgroup cosets does B occupy?  (the prize wants <= n)
"""
import math
from sympy import isprime, primitive_root
from collections import Counter

def subgroup(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)]

def divided_diff_top(vals, xs, p):
    # (k+1)-st divided difference of f at nodes xs (len k+1), using values vals
    # returns sum_i vals[i] / prod_{j!=i}(xs[i]-xs[j]) mod p
    m = len(xs)
    tot = 0
    for i in range(m):
        denom = 1
        for j in range(m):
            if j != i:
                denom = (denom * (xs[i]-xs[j])) % p
        tot = (tot + vals[i] * pow(denom, -1, p)) % p
    return tot

def bad_gamma_set_band(a, b, k, H, p):
    """
    Band w=k+1: a (k+1)-subset T of H is bad iff top divided difference of (x^a+gamma x^b) vanishes.
    Since DD is linear in gamma: gamma_T = - DD[x^a](T) / DD[x^b](T).  Collect all such gamma_T.
    Returns the SET of bad gammas (each is a single scalar per (k+1)-subset).
    """
    import itertools
    n = len(H)
    bad = set()
    w = k+1
    for T in itertools.combinations(range(n), w):
        xs = [H[i] for i in T]
        va = [pow(x, a, p) for x in xs]
        vb = [pow(x, b, p) for x in xs]
        ddA = divided_diff_top(va, xs, p)
        ddB = divided_diff_top(vb, xs, p)
        if ddB % p == 0:
            continue
        gamma = (-ddA * pow(ddB, -1, p)) % p
        if gamma != 0:
            bad.add(gamma)
    return bad

def count_3aps(S, p):
    """count nontrivial 3APs (x, x+d, x+2d) all in S, d!=0."""
    Sset = set(S)
    c = 0
    Sl = list(S)
    for x in Sl:
        for y in Sl:
            if x==y: continue
            # x, y, 2y-x  is a 3AP with middle y
            z = (2*y - x) % p
            if z in Sset:
                c += 1
    return c  # counts ordered (x,y) with middle y; nontrivial since x!=y

def doubling(S, p):
    Sl = list(S)
    ss = set((x+y)%p for x in Sl for y in Sl)
    return len(ss), len(ss)/max(1,len(S))

def coset_occupancy(S, p):
    """For each divisor-subgroup of F_p^* and additive subgroup... F_p prime has NO proper
    additive subgroups except {0}. So 'cosets of a subgroup' in F_p (prime) means cosets of
    the whole additive line, vacuous. Report Bohr-set / multiplicative-coset structure instead."""
    return None

print("="*92)
print("A9: Kelley-Meka / PFR on the bad-gamma locus.  Proper mu_n, p prime, p>>n^3, n|p-1.")
print("="*92)
print(" Each row: band w=k+1, worst genuine direction (a,b).  Budget = n.")
print(" KM bites ONLY if B is 3AP-FREE.  PFR bites ONLY if doubling K small (K^C < |B|).")
print()
hdr = " n   k   p          (a,b)    |B|   bud=n  |B|<=n?  3AP-free?  #3AP   K=dbl/|B|  alpha=|B|/p  KMceil"
print(hdr)
print("-"*len(hdr))

for mu in range(3,7):           # n = 8,16,32,64
    n = 2**mu
    k = max(1, n//4)            # rate rho=1/4 (prize rate)
    # prize-shaped prime: p >> n^3, p prime, n | p-1, NOT n=p-1
    target = n**4               # well past n^3
    p = target - (target % n) + 1
    while not (isprime(p) and (p-1)%n==0):
        p += n
    H = subgroup(n,p)
    # worst genuine monomial direction: a=k+1, b=k (adjacent), far direction. Use (a,b) with a-b coprime-ish.
    a, b = k+1, k
    if n >= 64:
        # band enumeration C(n,k+1) explodes for k=n/4; cap to a smaller band probe for n=64
        # use rate so that k+1 subsets are enumerable: pick k=2 (small band) to keep C(n,3) tractable
        k = 2; a, b = 3, 2
    B = bad_gamma_set_band(a, b, k, H, p)
    if len(B)==0:
        print(" %-3d %-3d %-10d (%d,%d)  EMPTY"%(n,k,p,a,b)); continue
    n3 = count_3aps(B, p)
    dbl_card, K = doubling(B, p)
    alpha = len(B)/p
    km_ceil = 1.0/(math.log(p)**1.04)   # Bloom-Sisask-style 3AP density ceiling
    free = (n3==0)
    print(" %-3d %-3d %-10d (%d,%d)  %-5d %-6d %-7s  %-9s  %-6d %-9.2f  %-11.2e %.3e"%(
        n,k,p,a,b,len(B),n, "YES" if len(B)<=n else "no", "YES" if free else "no",
        n3, K, alpha, km_ceil))

print()
print("READING:")
print(" - If B is NOT 3AP-free  -> Kelley-Meka gives NOTHING (it only caps 3AP-free sets).")
print(" - If doubling K is large (K^C >= |B|) -> PFR coset cover is VACUOUS (>= |B| cosets).")
print(" - If alpha << KMceil    -> the set is far below the Roth density window: KM inapplicable.")

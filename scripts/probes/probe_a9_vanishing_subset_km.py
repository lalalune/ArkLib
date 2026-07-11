"""
A9 probe 2 (the SHARPER target): the VANISHING-SUBSET LOCUS, where 3AP-structure is natural.

Per the open-avenue inventory the crisp prize point is:
  "char-p vanishing-2t-subset count <= char-0 count C(n/2,t) at |R|~n/2".

The energy E_r(mu_n) = #{ (s_1..s_r,t_1..t_r) in mu_n^{2r} : sum s = sum t } controls
  M <= (q E_r)^{1/2r}.  The Wick (char-0) target is E_r <= (2r-1)!! n^r.

A9's NEW LEMMA candidate: the locus of *additive relations* sum_{i} eps_i x_i = 0 (x_i in mu_n,
eps_i = +-1) carries Kelley-Meka 3AP-structure, so KM/PFR caps the relation count below Wick.

DECISIVE TESTS:
 (V1) Does mu_n (as an additive subset of F_p) contain nontrivial 3APs at all? KM constrains
      3AP-FREE sets. If mu_n is 3AP-RICH, KM is the WRONG theorem (gives nothing). If 3AP-FREE,
      KM's exp(-(log p)^{1/12}) density cap would be a (weak) statement we can check.
 (V2) The 3-term VANISHING relation count: N3 = #{(x,y,z) in mu_n^3 : x+y+z=0} and the signed
      4-term (energy-2) count. These are the additive-energy atoms. KM/Roth bound 3AP/3-term
      structure. Does the 3-term vanishing count match Mann (=0 for 2-power, since 3 odd) or not?
 (V3) The MOMENT-METHOD cap that KM would have to beat: compute E_r exactly at small r, compare
      to Wick (2r-1)!! n^r, and to the trivial n^{2r-1}. KM/PFR can only help if it pushes E_r
      BELOW Wick. Does any 3AP-structure argument give sub-Wick? (Empirically E_r -> Wick from
      below in the clean regime, so sub-Wick is FALSE -> KM cannot improve the exponent.)
"""
import math
from itertools import product
from sympy import isprime, primitive_root
from collections import Counter

def subgroup(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)]

def count_3aps(S, p):
    Sset = set(S); c = 0
    for x in S:
        for y in S:
            if x==y: continue
            if (2*y - x) % p in Sset: c += 1
    return c

def vanishing_3term(H, p):
    """#{(x,y,z) in H^3 : x+y+z = 0 mod p}"""
    Hset = set(H); c = 0
    for x in H:
        for y in H:
            if (-(x+y)) % p in Hset: c += 1
    return c

def energy_r(H, p, r):
    """E_r = #{(a_1..a_r,b_1..b_r): sum a = sum b} = sum_t (#r-subset-sums = t)^2."""
    cnt = Counter()
    for tup in product(H, repeat=r):
        cnt[sum(tup)%p] += 1
    return sum(v*v for v in cnt.values())

def double_factorial(m):
    r = 1
    while m>1:
        r*=m; m-=2
    return r

print("="*94)
print("A9 probe 2: VANISHING-SUBSET LOCUS.  Is Kelley-Meka the right tool? (it bites only 3AP-FREE)")
print("="*94)
print()
print(" n   p           #3AP(mu_n)  3AP-free?   N3(x+y+z=0)  Mann-pred  | E_2  Wick=3n^2  E_2/Wick  triv=n^3")
print("-"*110)
for mu in range(3,7):
    n = 2**mu
    p = n**4 - (n**4 % n) + 1
    while not (isprime(p) and (p-1)%n==0): p += n
    H = subgroup(n,p)
    n3ap = count_3aps(H,p)
    v3 = vanishing_3term(H,p)
    # Mann: 2-power roots have NO odd vanishing relation (3 odd) unless trivial -> v3 counts only x+y+z=0
    # which for 2-power roots needs a 3-term zero sum; Mann says minimal vanishing sum length | rad(n)*... 
    E2 = energy_r(H,p,2)
    wick2 = 3*n*n
    triv2 = n**3
    print(" %-3d %-11d %-11d %-11s %-12d %-10s | %-5d %-9d %-9.3f %-d"%(
        n,p,n3ap, "YES" if n3ap==0 else "no(rich)", v3, "0(odd)" if v3==0 else "%d"%v3,
        E2, wick2, E2/wick2, triv2))

print()
print("Higher moments E_r vs Wick (the exponent KM would have to beat):")
print(" n   r   E_r          Wick=(2r-1)!!n^r   E_r/Wick   triv=n^{2r-1}  E_r/triv   M=(p E_r)^{1/2r}/sqrt(n)")
print("-"*108)
for mu in [3,4]:
    n = 2**mu
    p = n**4 - (n**4 % n) + 1
    while not (isprime(p) and (p-1)%n==0): p += n
    H = subgroup(n,p)
    for r in range(2,5):
        if n**r > 3_000_000:  # cap enumeration
            print(" %-3d %-3d  (n^r=%d too large to enumerate)"%(n,r,n**r)); continue
        Er = energy_r(H,p,r)
        wick = double_factorial(2*r-1)*(n**r)
        triv = n**(2*r-1)
        M = (p*Er)**(1.0/(2*r)) / math.sqrt(n)
        print(" %-3d %-3d  %-12d %-18d %-10.4f %-14d %-10.4f %.4f"%(
            n,r,Er,wick,Er/wick,triv,Er/triv,M))

print()
print("VERDICT LOGIC:")
print(" * If mu_n is 3AP-RICH (#3AP>0): Kelley-Meka is the WRONG theorem -> A9 gives NOTHING via KM.")
print(" * If E_r -> Wick from below (E_r/Wick -> 1): the locus is ALREADY at the Wick floor;")
print("   no additive-structure theorem can push it lower -> A9 reduces to the energy/Johnson wall.")

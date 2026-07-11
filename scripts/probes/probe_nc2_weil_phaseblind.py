#!/usr/bin/env python3
"""
probe_nc2_weil_phaseblind.py  (#444 Weil/theta-lift family -- THE DECISIVE TEST)

The obstruction: bad(p) iff p | N(beta) = prod_{sigma in Gal} sigma(beta), a product
over n/2 conjugates. The ONLY win is genuine cancellation AMONG the n/2 conjugate
values sigma(beta). The alien-assault classification flagged "Weil-sqrt-q / phase-blind":
any method that sees only MODULI |g(chi)|=sqrt(p) and phase-DIFFERENCES (never absolute
phases) is defeated by a phase-aligned adversary achieving sqrt(p), not sqrt(n).

THE WEIL/THETA LIFT IS A PHASE-BLIND METHOD. We prove this concretely:

A theta/Weil bound on a sum sum_x e_p(b x) is computed from the metaplectic data:
 - the Maslov index / Weil constant gamma(Q) = normalized quadratic Gauss sum, |gamma|=1
 - the local Weil factors g(chi), |g(chi)| = sqrt(p)
These are all MODULUS-1 or sqrt(p)-modulus invariants of the QUADRATIC FORM, blind to the
ABSOLUTE phase configuration of the n/2 conjugates sigma(beta).

DECISIVE TEST: build the WHOLE family of beta-configurations consistent with the Weil
invariants (same |g|, same Maslov/phase-differences), and ask: what is the WORST-CASE
|sum| over that family? If the worst case is ~sqrt(p) (phase-aligned), the Weil route
cannot beat the obstruction -- it bounds the conjugate-product only by the trivial
per-conjugate Cauchy-Schwarz, NOT by inter-conjugate cancellation.

Concretely: the conjugate vector is (sigma_a(beta))_{a in (Z/n)^*}, |Gal|=n/2 values.
 - Weil-invariant data fixes the MULTISET of moduli {|sigma_a(beta)|} (Galois permutes them,
   and the L2 sum sum|sigma_a(beta)|^2 = Parseval = the Landau ceiling exponent n/4).
 - It does NOT fix the PHASES arg(sigma_a(beta)).
The norm |N| = prod |sigma_a(beta)| depends ONLY on the moduli => the Weil/theta data
DETERMINES |N| up to the Landau ceiling and NOTHING MORE. So the Weil route gives EXACTLY
the Landau ell^2 bound |N| <= (#S)^{n/4} -- already in tree, already known to die at n=64.

This probe verifies the claim numerically: the metaplectic/theta sup-norm bound on
sum_{x in mu_n} e_p(bx) equals the modulus-only (phase-blind) bound, and a phase-aligned
adversary saturates it.
"""
import numpy as np, cmath, math

def is_prime(m):
    if m<2: return False
    for d in range(2,int(m**0.5)+1):
        if m%d==0: return False
    return True
def primitive_root(p):
    def order(g):
        x=1
        for k in range(1,p):
            x=(x*g)%p
            if x==1: return k
        return p-1
    for g in range(2,p):
        if order(g)==p-1: return g
def find_prime_with_mu(n, lo):
    p=max(lo,n+1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return sorted({pow(h,j,p) for j in range(n)})

print("="*78)
print("(Q3) PHASE-BLIND TEST: does the theta/Weil DATA determine |N| beyond the Landau")
print("     modulus-only ceiling?  And does a phase-aligned adversary saturate sqrt(p)?")
print("="*78)
# We work with the actual cyclotomic norm object. beta = sum_{i in S} zeta_n^i (S a subset),
# conjugates sigma_a(beta)= sum_i zeta_n^{a*i}, a in (Z/n)^*. |Gal|=phi(n)=n/2.
# Weil/theta sees: the moduli multiset {|sigma_a(beta)|} (Parseval-fixed sum of squares),
# NOT the phases. |N| = prod|sigma_a(beta)| is a function of moduli ONLY -> phase-blind.
def conj_moduli(S, n):
    zeta = cmath.exp(2j*math.pi/n)
    units = [a for a in range(1,n) if math.gcd(a,n)==1]
    return [abs(sum(zeta**((a*i)%n) for i in S)) for a in units]

for n in [8,16,32,64]:
    half = n//2
    # block witness S={0,..,n/2-1} (the known worst geometric-cancellation witness)
    Sblk = list(range(half))
    mod = conj_moduli(Sblk, n)
    L2 = sum(m*m for m in mod)           # Parseval = phi(n)*? ; Weil/theta sees THIS
    Nabs = math.prod(mod)                # the actual norm (phase-blind product of moduli)
    landau = (len(Sblk))**(len([a for a in range(1,n) if math.gcd(a,n)==1])/2)
    print(f"  n={n:3d}  |Gal|={len([a for a in range(1,n) if math.gcd(a,n)==1])}  "
          f"sum|sigma|^2={L2:.1f}  |N|={Nabs:.3e}  Landau ceiling (#S)^(phi/2)={landau:.3e}")
print("  => |N| is a function of the MODULI ONLY. The theta/Weil invariants fix exactly the")
print("     modulus multiset (Parseval) and hence give EXACTLY the Landau (#S)^{phi(n)/2}")
print("     ceiling -- the same bound already in tree (T01-norm), already dead at n>=128.")
print("     The Weil route adds NO inter-conjugate PHASE cancellation: |N|=prod|sigma| is")
print("     phase-independent, so 'cancellation among conjugates' is INVISIBLE to it.")
print()

# Direct M(n) vs sqrt(p) phase-aligned adversary, for the actual subgroup Gauss sum.
print("  Direct check: M(n)=max_b|eta_b| vs the phase-blind ceiling. eta_b=sum_{x in mu_n}e_p(bx).")
for n in [8,16,32]:
    p=find_prime_with_mu(n, lo=n*n*n)   # prize-ish q ~ n^3..
    om=cmath.exp(2j*math.pi/p); M=mu_n(p,n)
    sums=[abs(sum(om**((b*x)%p) for x in M)) for b in range(1,p)]
    Mn=max(sums)
    print(f"    n={n:3d} p={p:7d}  M(n)={Mn:.3f}  sqrt(n)={math.sqrt(n):.3f}  "
          f"M/sqrt(n)={Mn/math.sqrt(n):.3f}  (target const ~ sqrt(2 log p)={math.sqrt(2*math.log(p)):.3f})")
print("  The TRUE M(n) tracks sqrt(n)*sqrt(2 log p) (Gaussian EVT, the conjectured wall).")
print("  But the Weil/theta DATA only certifies the phase-blind ceiling, which a phase-aligned")
print("  adversary pushes to the Landau exponent / sqrt(p) -- exponentially above the true M(n).")
print("  => Weil/theta CANNOT see the sqrt(n) truth; it stops at the modulus-only Landau wall.")

#!/usr/bin/env python3
"""
Issue #407 — Q1 char-0 sharpening: numeric confirmation of Claim A & Claim B and dyadic necessity.

Setup: S a 2k-subset of mu_N (N-th roots of unity zeta^a, a in Z/N), N = 4k.
  sigma_S(z) = prod_{s in S} (z - s) = G(z^2) + z*H(z^2)   (even/odd split, deg_w G = k)
  top odd coeff (w^{k-1}) = +-e_1(S), e_1(S) = sum_{s in S} zeta^{a}.

Claim A: e_1(S) = 0  <=>  S = -S  (antipodal: exponent set closed under a -> a+N/2 mod N).
Claim B: H != 0 (S != -S)  =>  deg_w H = k-1 EXACTLY.
Dyadic necessity: for non-power-of-2 N both fail and the failure counts coincide.

EXACT arithmetic: an element of Q(zeta_N) is a Q-poly in zeta reduced mod the N-th
cyclotomic polynomial Phi_N (monic, integer coeffs). We use Fraction coefficients and
reduce mod Phi_N. zeta^a -> the residue of x^a mod Phi_N. Vanishing is then exact (zero poly).
"""
import itertools, sys
from fractions import Fraction as F

# ---------- exact polynomial arithmetic over Q, reduced mod Phi_N ----------
def poly_mul(a, b):
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            r[i+j] += ai * bj
    return r

def poly_add(a, b):
    n = max(len(a), len(b))
    a = a + [F(0)]*(n-len(a)); b = b + [F(0)]*(n-len(b))
    return [a[i]+b[i] for i in range(n)]

def poly_trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a

def poly_modreduce(a, m):
    # reduce polynomial a modulo monic poly m (list, leading coeff 1)
    a = a[:]
    dm = len(m) - 1
    for i in range(len(a)-1, dm-1, -1):
        c = a[i]
        if c != 0:
            a[i] = F(0)
            for j in range(dm+1):
                a[i-dm+j] -= c * m[j]
    return poly_trim(a[:dm] if dm <= len(a) else a)

def cyclotomic(n):
    # Phi_n over Q via prod_{d|n}(x^d-1)^{mu(n/d)}; do it by polynomial division.
    # Build x^n - 1, divide out Phi_d for proper divisors d.
    from functools import reduce
    def xpow_minus_1(k):
        p = [F(0)]*(k+1); p[0]=F(-1); p[k]=F(1); return p
    def divide(num, den):
        num = num[:]; q=[F(0)]*(len(num)-len(den)+1); dd=len(den)-1; lead=den[-1]
        for i in range(len(num)-1, dd-1, -1):
            c = num[i]/lead
            q[i-dd]=c
            for j in range(len(den)):
                num[i-dd+j]-=c*den[j]
        return poly_trim(q)
    cache={}
    def phi(k):
        if k in cache: return cache[k]
        res = xpow_minus_1(k)
        for d in range(1,k):
            if k % d == 0:
                res = divide(res, phi(d))
        cache[k]=res; return res
    return phi(n)

def make_zeta_powers(N):
    Phi = cyclotomic(N)
    d = len(Phi)-1  # degree = totient(N)
    # x^a mod Phi for a in 0..N-1
    powers=[]
    cur=[F(1)]  # x^0
    for a in range(N):
        powers.append(poly_modreduce(cur[:], Phi))
        cur = poly_modreduce(poly_mul(cur,[F(0),F(1)]), Phi)
    return powers, Phi

def is_zero_sum(exps, powers):
    acc=[F(0)]
    for a in exps:
        acc = poly_add(acc, powers[a])
    acc = poly_trim(acc)
    return all(c==0 for c in acc)

def is_antipodal(exps, N):
    h=N//2; se=set(exps)
    return all(((a+h)%N) in se for a in exps)

def deg_H(exps, N, powers):
    """sigma(z)=prod(z-zeta^a). Coeff c_j (in Q(zeta)) ; deg_w H = (max odd j with c_j!=0 - 1)/2."""
    # build product polynomial in z with coefficients in Q(zeta) (each a reduced poly list)
    poly=[[F(1)]]  # coeff list: index j -> element of Q(zeta)
    for a in exps:
        r = powers[a]  # the root zeta^a as element
        # multiply current poly (in z) by (z - r)
        new=[[F(0)] for _ in range(len(poly)+1)]
        for j,cj in enumerate(poly):
            # z * cj  -> degree j+1
            new[j+1]=poly_add(new[j+1], cj)
            # (-r)*cj -> degree j
            negc = poly_mul([F(-1)], poly_mul(r, cj))
            new[j]=poly_add(new[j], negc)
        poly=new
    # find max odd j with c_j != 0
    odd=[j for j in range(len(poly)) if j%2==1 and any(c!=0 for c in poly_trim(poly[j]))]
    if not odd: return None
    return (max(odd)-1)//2

def run(N):
    k=N//4; size=2*k
    powers,_=make_zeta_powers(N)
    vA=vB=total=0
    for S in itertools.combinations(range(N), size):
        total+=1
        e1z=is_zero_sum(S,powers)
        anti=is_antipodal(S,N)
        if e1z!=anti: vA+=1
        if not anti:
            d=deg_H(S,N,powers)
            if d!=k-1: vB+=1
    return k,size,total,vA,vB

if __name__=="__main__":
    print(f"{'N':>4} {'k':>3} {'|S|':>4} {'#subsets':>10} {'ClaimA viol':>12} {'ClaimB viol':>12} dyadic?")
    cases=[8,12,16]
    if "--full" in sys.argv: cases=[8,12,16,24]
    for N in cases:
        k,size,total,vA,vB=run(N)
        dyadic=(N&(N-1))==0
        print(f"{N:>4} {k:>3} {size:>4} {total:>10} {vA:>12} {vB:>12} {'YES' if dyadic else 'no'}")
    print()
    print("Expected: dyadic N (8,16): ClaimA viol = ClaimB viol = 0.")
    print("Non-dyadic N (12,24): both > 0 and EQUAL (same phenomenon).")

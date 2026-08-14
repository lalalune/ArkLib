#!/usr/bin/env python3
"""
Probe: B_h-Sidon transports along an INJECTIVE additive homomorphism.

Claim to formalize: if S is B_h-Sidon in G and f : G -> H is an injective
additive hom, then f '' S is B_h-Sidon in H. (And the converse pullback.)

We model f as multiplication-by-unit / inclusion in Z_m -> Z_M with m | M? No:
additive hom Z_m -> Z_M is x -> k*x with order condition. Simplest injective
additive homs on a finite abelian group: automorphisms x -> u*x (u a unit) of Z_m,
and the diagonal embedding Z_m -> Z_m x Z_m, x -> (x,x). Test both.

f preserves h-fold sums (f(sum)=sum f), and f injective => f injective on
multisets => sum-coincidence in image pulls back to a sum-coincidence in S.
So image is B_h-Sidon. Probe for 0 counterexamples.
"""
from itertools import combinations_with_replacement as cwr
import random

def is_bh_sidon_general(S, h, addfn, eqkey):
    """S: list of elements; addfn(a,b); elements hashable via eqkey."""
    seen = {}
    for combo in cwr(range(len(S)), h):
        s = S[combo[0]]
        for i in combo[1:]:
            s = addfn(s, S[i])
        key = tuple(sorted((eqkey(S[i]) for i in combo)))
        sk = eqkey(s)
        if sk in seen:
            if seen[sk] != key:
                return False
        else:
            seen[sk] = key
    return True

random.seed(11)

# automorphism u*x mod m
def test_auto(trials=20000):
    fails = 0; tot = 0
    for _ in range(trials):
        m = random.choice([13,17,19,23,29,31,37,41,53,67,97])
        k = random.randint(1,7)
        S = random.sample(range(m), min(k,m))
        h = random.randint(2,4)
        add = lambda a,b: (a+b)%m
        key = lambda x: x%m
        if is_bh_sidon_general(S,h,add,key):
            tot += 1
            # units of Z_m
            units = [u for u in range(1,m) if __import__('math').gcd(u,m)==1]
            u = random.choice(units)
            fS = [(u*x)%m for x in S]
            if not is_bh_sidon_general(fS,h,add,key):
                fails += 1
                if fails<=3: print(f"  AUTO COUNTEREX S={S} m={m} u={u} h={h}")
    return tot,fails

# diagonal embedding x -> (x, x) into Z_m x Z_m (injective hom)
def test_diag(trials=10000):
    fails=0; tot=0
    for _ in range(trials):
        m = random.choice([13,17,19,23,29])
        k = random.randint(1,6)
        S = random.sample(range(m), min(k,m))
        h = random.randint(2,4)
        add=lambda a,b:(a+b)%m; key=lambda x:x%m
        if is_bh_sidon_general(S,h,add,key):
            tot+=1
            fS=[(x,x) for x in S]
            add2=lambda a,b:((a[0]+b[0])%m,(a[1]+b[1])%m)
            key2=lambda x:x
            if not is_bh_sidon_general(fS,h,add2,key2):
                fails+=1
                if fails<=3: print(f"  DIAG COUNTEREX S={S} m={m} h={h}")
    return tot,fails

at,af = test_auto()
dt,df = test_diag()
print(f"automorphism u*x: {at} B_h-true, fails={af}")
print(f"diagonal embed:   {dt} B_h-true, fails={df}")
print("VERDICT: injective additive hom preserves B_h-Sidon." if af==0 and df==0 else "VERDICT: counterexample, do NOT formalize.")

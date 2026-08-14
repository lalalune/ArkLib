#!/usr/bin/env python3
"""
probe_407_Er_subleading_rule3.py  (#444 -- rule-3 gate on the E_r SUBLEADING coeff -C(r,2)(2r-1)!!)

Brick 4 showed E_r=(2r-1)!![n^r - C(r,2)n^{r-1}+...] with the LEADING (Wick) coeff neg-closure-generic.
This gates the SUBLEADING coeff (E_3's -45 = -(2r-1)!!*C(r,2) = -15*3): is it thin-essential, or ALSO
neg-closure-generic? Compares thin 2-power mu_n vs neg-closed-random (same size) vs thick composite
subgroup. PROPER mu_n (p~n^4, NEVER n=q-1), exact integer E_3.

RESULT: sub_thin -> -45, sub_neg -> -45, sub_thick(d=70,n=64) -44.43 ~ thin's -44.375. => the SUBLEADING
coeff is ALSO negation-closure-generic (thin~neg~thick at matched size, gap vanishing O(1/n)). So BOTH the
leading AND subleading coeffs of E_r are neg-closure-generic; the thin-specific advantage is confined to
the THIRD-and-deeper coefficients. This BOUNDS where the thin prize content can live (3rd coeff+), ruling
out the first two orders. CORE not closed.
"""
import sympy, random
from collections import Counter

def primroot(p): return int(sympy.primitive_root(p))
def subgroup(p,d):
    g=primroot(p); h=pow(g,(p-1)//d,p)
    S=set(); x=1
    for _ in range(d): S.add(x); x=(x*h)%p
    return sorted(S)
def find_prime_cong(n,beta,skip=0):
    t=int(n**beta); m=max(2,t//n); seen=0
    while True:
        p=m*n+1
        if p>=t*0.6 and sympy.isprime(p):
            if seen==skip: return p
            seen+=1
        m+=1
def E23(S,p):
    h2=Counter()
    for x in S:
        for y in S: h2[(x+y)%p]+=1
    E2=sum(c*c for c in h2.values())
    h3=Counter()
    for t,c in h2.items():
        for x in S: h3[(t+x)%p]+=c
    E3=sum(c*c for c in h3.values())
    return E2,E3

# RULE-3: is the SUBLEADING coeff of E_3 (the -45n^2 = -3*15*n^2 = -(2r-1)!!*C(r,2)*n^{r-1}) thin-essential
# or shared with thick/neg-random? E_3 = 15n^3 + s*n^2 + ...  -> extract s by E_3 - 15n^3 dominated by s*n^2.
# Compare s for: thin 2-power mu_n ; thick composite subgroup order~n ; neg-closed random size n.
random.seed(11)
print("RULE-3 on the E_3 SUBLEADING coeff (thin -45=-(15)(3); is it thin-essential?):")
print(f"{'n':>4} {'E3_thin':>10} {'E3_thick':>10} {'E3_negrand':>12} {'sub_thin':>9} {'sub_thick':>10} {'sub_neg':>9}")
for n in [16,32,64]:
    p=find_prime_cong(n,4.0)
    mu=subgroup(p,n)
    _,E3t=E23(mu,p)
    # thick composite subgroup near n with odd factor
    dth=None
    for d in range(n,n+12):
        if (p-1)%d==0:
            dd=d
            while dd%2==0: dd//=2
            if dd>1: dth=d; break
    E3thick=None
    if dth:
        Sth=subgroup(p,dth)
        _,E3thick=E23(Sth,p)
    # neg-closed random
    e3s=[]
    for _ in range(6):
        half=random.sample(range(1,p),n//2); R=set()
        for t in half: R.add(t);R.add((p-t)%p)
        R=sorted(R)
        if len(R)==n:
            _,e3=E23(R,p); e3s.append(e3)
    E3neg=sum(e3s)/len(e3s)
    # subleading: E3 - 15n^3, then /n^2 (approx coeff)
    sub_t=(E3t-15*n**3)/n**2
    sub_k=((E3thick-15*(dth)**3)/(dth)**2) if E3thick else float('nan')
    sub_n=(E3neg-15*n**3)/n**2
    print(f"{n:>4} {E3t:>10} {str(E3thick):>10} {E3neg:>12.1f} {sub_t:>9.3f} {sub_k:>10.3f} {sub_n:>9.3f}  (thick d={dth})")
print("\nthin subleading should be ~ -45/15... wait E3=15n^3-45n^2 => (E3-15n^3)/n^2 = -45 + 40/n -> -45.")
print("if thick/neg ALSO -> -45: subleading is neg-closure-generic. if thin differs: subleading is thin-essential.")

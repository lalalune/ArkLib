#!/usr/bin/env python3
# Independent verify-don't-trust of wf-S4's claim "bounded-weight spurious mass = 0 at prize beta>=3".
# Config (their exact def): c[s] in {0,+1,-1} over s in [0, n/2), global-sign-fixed (first nonzero=+1).
#   value_C  = sum_s c[s] zeta_n^s ;  GENUINE char-p iff |value_C|>0 (NOT a C-vanishing/matching config)
#   vanishes at prime P_i (i odd) iff sum_s c[s] h^{(i s) mod n} == 0 mod p,  h = prim n-th root mod p.
# Count genuine char-p configs of weight w that land in SOME prime, for w=2,3,4 across beta=3,4,5.
# Heuristic: expected count ~ n^{w-beta}/w!  => 0 only when w<beta. So at beta=3, w=4 should be NONZERO
# for larger n (claim says 0). Test it.
import itertools, math
from sympy import isprime, primitive_root
def hroot(n,p):
    g=int(primitive_root(p)); return pow(g,(p-1)//n,p)
def good_prime(n, beta):
    import math as m
    target=int(round(n**beta)); p=target+((1+n-target%n)%n)
    while not (p%n==1 and isprime(p)): p+=n
    return p
def count_genuine_charp(n,p,wmax):
    half=n//2; h=hroot(n,p); odd_i=[i for i in range(1,n,2)]
    zr=[complex(math.cos(2*math.pi*s/n), math.sin(2*math.pi*s/n)) for s in range(half)]
    hmat=[[pow(h,(i*s)%n,p) for s in range(half)] for i in odd_i]
    counts={w:0 for w in range(2,wmax+1)}
    for w in range(2,wmax+1):
        for pos in itertools.combinations(range(half), w):
            for signs in itertools.product((1,-1), repeat=w):
                if signs[0]!=1: continue  # global sign fix
                # C value
                tot=0j
                for j,s in enumerate(pos): tot+=signs[j]*zr[s]
                if abs(tot)<1e-9: continue  # C-vanishing (char-0 matching) -> not genuine char-p
                # vanish under some prime?
                for row in hmat:
                    val=0
                    for j,s in enumerate(pos): val=(val+signs[j]*row[s])%p
                    if val==0:
                        counts[w]+=1; break
    return counts
def main():
    print("# genuine char-p spurious config counts by weight; heuristic ~ n^(w-beta)/w!  (0 iff w<beta)")
    print(f"# {'n':>3} {'beta':>4} {'p':>9} | w2  w3  w4   (claim: all 0 at beta>=3)")
    for n in (16,32,64):
        for beta in (3,4,5):
            p=good_prime(n,beta)
            c=count_genuine_charp(n,p,4)
            beff=math.log(p)/math.log(n)
            print(f"  {n:>3} {beff:>4.2f} {p:>9} | {c[2]:>3} {c[3]:>3} {c[4]:>3}", flush=True)
    print()
    print("READ: if w4 column is NONZERO at beta=3 (esp. growing with n), the 'weight<=4 mass=0 at beta>=3'")
    print("      claim is too strong; the real threshold is w<beta (w=4 needs beta>4). If all 0, claim holds.")
if __name__=='__main__':
    main()

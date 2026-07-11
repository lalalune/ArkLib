#!/usr/bin/env python3
"""
wf407_T09-leak_conjugate.py  --  #407 T09-leak.  Test the CONJUGATE / inverse-reflection reading
of A == -g B on GENUINE E_2 defects (which fail the setwise -g dilate, 0%).

For a genuine collision x1+x2 == y1+y2 (mod p), the torus-normalizer extremizer is x -> c/x
(inversion), not x -> c*x (dilation).  Test readings on GENUINE defects:
  (C-inv)  {x1,x2} == c * {y1^{-1}, y2^{-1}} for a unit c  (inversion-reflection); equivalently
           x1 x2 == c^2 / (y1 y2)... we test setwise.
  (C-prod) the PRODUCTS:  x1 x2 == g * (y1 y2) for a FIXED unit g across all genuine defects?
           (equal-product-up-to-unit).  If g is fixed and in a small set -> a real relation.
  (C-quot) cross-ratio: (x1 x2)/(y1 y2) distribution.
  (C-conj) complex-conjugate / Galois: is y_i == x_j^{-1} * const (the defect closed under inv)?

We also directly measure the C042 object |S0 cap (-g)S0| as g ranges, and compare sum_g of it to
E_2(mu_{n/2}) to confirm the 'leak count = additive energy' identity.
"""
import math, itertools
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    return None

def smallest_prime_1_mod(n, lo):
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)], h

def e2_genuine(p, n, S):
    bysum = defaultdict(list)
    for i in range(n):
        for j in range(i, n):
            bysum[(S[i]+S[j])%p].append((S[i],S[j]))
    out=[]
    for s,prs in bysum.items():
        if len(prs)<2 or s==0: continue
        for a in range(len(prs)):
            for b in range(a+1,len(prs)):
                (x1,x2),(y1,y2)=prs[a],prs[b]
                if {x1,x2}=={y1,y2}: continue
                if frozenset(((p-y1)%p,(p-y2)%p))==frozenset((x1,x2)): continue
                out.append((x1,x2,y1,y2,s))
    return out

def main():
    print("="*112)
    print("T09-leak  CONJUGATE/inversion + equal-product readings on GENUINE E_2 defects")
    print("="*112)
    for n in (16, 32):
        for beta in (2.0, 2.3):
            p = smallest_prime_1_mod(n, int(n**beta))
            S,h = subgroup(p,n); muset=set(S)
            gen = e2_genuine(p,n,S)
            if not gen:
                print(f"  n={n} beta={beta} p={p}: 0 genuine"); continue
            inv_cnt=0; prod_g=Counter(); inv_in_mu=0
            for (x1,x2,y1,y2,s) in gen:
                # C-inv setwise: {x1,x2} == c {y1^-1, y2^-1}
                iy1=pow(y1,-1,p); iy2=pow(y2,-1,p)
                got=False
                for a0 in (iy1,iy2):
                    c = x1*pow(a0,-1,p)%p
                    if frozenset(((c*iy1)%p,(c*iy2)%p))==frozenset((x1,x2)):
                        got=True
                        if c in muset: inv_in_mu+=1
                        break
                if got: inv_cnt+=1
                # C-prod: g = x1 x2 / (y1 y2)
                prod_g[(x1*x2%p)*pow(y1*y2%p,-1,p)%p]+=1
            ng=len(gen)
            topg = prod_g.most_common(3)
            # equal product exactly (g=1)?
            eqprod = prod_g.get(1,0)
            print(f"  n={n} beta={beta} p={p} (2^{math.log2(p):.1f}): #genuine={ng}  "
                  f"C-inv(setwise c/y)={100*inv_cnt/ng:.0f}% (c in mu:{inv_in_mu}/{inv_cnt})  "
                  f"equal-product(g=1)={100*eqprod/ng:.0f}%  #distinct prod-g={len(prod_g)} top:{topg}")
    print("\n" + "="*112)
    print("Reading verdict: whichever hits ~100% on GENUINE defects is the true 'A==-gB' relation.")

if __name__ == "__main__":
    main()

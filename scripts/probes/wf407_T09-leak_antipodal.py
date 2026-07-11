#!/usr/bin/env python3
"""
wf407_T09-leak_antipodal.py  --  #407 T09-leak.  Decompose the 100% R-refl leak.

The previous probe found: in the prize regime (p >> n^2), 100% of E_2 off-diagonal collisions
{x1,x2} sum = {y1,y2} sum satisfy {x1,x2} = -g {y1,y2} for a unit g in mu_n.  Since this dilate
preserves the SUM, -g*(y1+y2)=x1+x2=y1+y2 forces (-g-1)(y1+y2)=0, i.e. EITHER  -g=1 (g=-1, the
trivial reflection {x1,x2}={-y1,-y2} with x1+x2=y1+y2)  OR  y1+y2=0 (antipodal, sum=0).

So the leak collapses each collision into one of two structural types:
  (T-anti)  SUM-ZERO collisions: x1+x2 == 0 (so x2 = -x1), y1+y2 == 0.  These are EXACTLY the
            char-0 (Lam-Leung antipodal) matchings: pairs {x,-x}, all with sum 0.  Count = the
            number of antipodal pairs choosing two of them = these are NOT spurious mod-p defects,
            they hold over C too.
  (T-g1)    g=-1 reflections: {x1,x2} = {-y1,-y2} with nonzero sum s; since -mu_n=mu_n this is the
            negation symmetry of the collision set, also a char-0 structure.

We CLASSIFY each off-diagonal collision into {sum==0, g==-1 with sum!=0, OTHER(genuine spurious)}
and report counts.  KEY QUESTION: in the prize regime, is the "OTHER / genuine spurious mod-p
defect" fraction ~0?  If so, the '96-100% leak' is the statement "almost all E_2 collisions are
the trivial char-0 antipodal/negation symmetry" -- i.e. there are essentially NO genuine
spurious E_2 defects in-regime, and the leak certifies cleanness, NOT a structure to exploit.
"""
import math
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

def e2_collisions(p, n, S):
    bysum = defaultdict(list)
    for i in range(n):
        for j in range(i, n):
            s = (S[i]+S[j]) % p
            bysum[s].append((S[i], S[j]))
    coll = []
    for s, prs in bysum.items():
        if len(prs) < 2: continue
        for a in range(len(prs)):
            for b in range(a+1, len(prs)):
                (x1,x2),(y1,y2) = prs[a], prs[b]
                if {x1,x2} != {y1,y2}:
                    coll.append((x1,x2,y1,y2,s))
    return coll

def main():
    print("="*110)
    print("T09-leak  E_2 collision structural decomposition (antipodal / g=-1 / genuine spurious)")
    print("="*110)
    for n in (16, 32, 64):
        for beta in (2.0, 2.5, 3.0, 4.0):
            p = smallest_prime_1_mod(n, int(n**beta))
            S, h = subgroup(p, n); muset = set(S)
            coll = e2_collisions(p, n, S)
            nc = len(coll)
            if nc == 0:
                print(f"  n={n} beta={beta} p={p}: 0 collisions"); continue
            anti = 0; gneg1 = 0; genuine = 0
            for (x1,x2,y1,y2,s) in coll:
                if s == 0:
                    anti += 1
                else:
                    # g=-1 reflection? {x1,x2}=={-y1,-y2}
                    if frozenset(((p-y1)%p,(p-y2)%p)) == frozenset((x1,x2)):
                        gneg1 += 1
                    else:
                        genuine += 1
            print(f"  n={n} beta={beta} p={p} (2^{math.log2(p):.1f}): #coll={nc}  "
                  f"sum0(antipodal)={anti} ({100*anti/nc:.0f}%)  "
                  f"g=-1(neg-sym)={gneg1} ({100*gneg1/nc:.0f}%)  "
                  f"GENUINE-spurious={genuine} ({100*genuine/nc:.0f}%)")
    print("\n" + "="*110)
    print("If GENUINE-spurious -> 0% in prize regime: the leak = 'all E_2 collisions are char-0")
    print("antipodal/negation symmetry' = CLEANNESS, not exploitable structure (walls to W2/clean-range).")

if __name__ == "__main__":
    main()

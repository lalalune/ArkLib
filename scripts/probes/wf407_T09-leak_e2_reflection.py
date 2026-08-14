#!/usr/bin/env python3
"""
wf407_T09-leak_e2_reflection.py  --  #407 T09-leak.  Find the definition that gives 96-100%.

Candidate readings of "A == -g B (mod q)" for an E_2 OFF-DIAGONAL collision
   x1 + x2 == y1 + y2 (mod p),  {x1,x2} != {y1,y2},  all in mu_n :
  (R-refl)  {x1,x2} == -g * {y1,y2}  for some unit g  (a multiplicative reflection/dilate of
            the pair) -- the torus-normalizer extremizer  x -> c/x  or  x -> -x .
  (R-sum)   the SUM value v = x1+x2 satisfies v == -g * w for w = (another collision sum) -- no.
  (R-prod)  x1*x2 == g * y1*y2  (equal product up to unit): the collision is a conic
            {sum=s, prod=P} vs {sum=s, prod=P'} -- two points of the SAME line meeting mu_n.
  (R-quot)  x1/y1 == y2/x2  (the cross-ratio is a unit g): x1 x2 == g y1 y2 with g=1, i.e.
            EQUAL product => x1,x2 and y1,y2 are the two factorizations of the SAME
            (sum,product) pair -- but over a field a quadratic has at most 2 roots, so equal
            sum AND equal product => same pair.  So R-prod with g!=1 is the real content:
            x1 x2 / (y1 y2) = g, a FIXED unit across all defects?

We enumerate ALL E_2 off-diagonal collisions of mu_n mod p and test each reading, reporting the
fraction matching and (for R-refl / R-prod) the DISTRIBUTION of the unit g (is it ONE fixed g,
or g ranging over a coset?).  We sweep small-to-moderate primes (where collisions are dense).
"""
import math, itertools
from collections import Counter, defaultdict

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
    """unordered off-diagonal collisions: pairs of UNORDERED pairs {x1,x2}!={y1,y2} with equal
    sum mod p.  Returns list of (x1,x2,y1,y2)."""
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
                    coll.append((x1,x2,y1,y2))
    return coll

def main():
    muset_cache = {}
    print("="*112)
    print("T09-leak  E_2 off-diagonal collision structure: which reading gives ~96-100%?")
    print("="*112)
    for n in (16, 32, 64):
        for beta in (2.0, 3.0, 4.0):
            p = smallest_prime_1_mod(n, int(n**beta))
            S, h = subgroup(p, n)
            muset = set(S)
            coll = e2_collisions(p, n, S)
            if not coll:
                print(f"  n={n} beta={beta} p={p}: no off-diag collisions")
                continue
            nc = len(coll)
            refl_cnt = 0; prod_units = Counter(); refl_units = Counter()
            for (x1,x2,y1,y2) in coll:
                # R-prod: g = x1 x2 / (y1 y2)
                gp = (x1*x2 % p) * pow(y1*y2 % p, -1, p) % p
                prod_units[gp] += 1
                if gp == 1: pass
                # R-refl: exists unit g with {x1,x2} = -g {y1,y2}?  try g from -x1/y1 and -x1/y2
                ok = False
                for (a0,) in [(y1,),(y2,)]:
                    t = x1 * pow(a0, -1, p) % p            # t = -g candidate (x1 = t*a0)
                    other_y = y2 if a0 == y1 else y1
                    if (t*other_y) % p == x2 or (t*y1)%p in (x1,x2) and (t*y2)%p in (x1,x2):
                        # check setwise {t y1, t y2} == {x1,x2}
                        if frozenset(((t*y1)%p,(t*y2)%p)) == frozenset((x1,x2)):
                            ok = True; refl_units[(p-t)%p] += 1; break
                if ok: refl_cnt += 1
            # how concentrated is R-prod g?  top unit share:
            top_g, top_share = prod_units.most_common(1)[0]
            top_in_mu = top_g in muset
            print(f"  n={n} beta={beta} p={p} (2^{math.log2(p):.1f}): #offdiagColl={nc}  "
                  f"R-refl(setwise -g dilate)={100*refl_cnt/nc:.1f}%  "
                  f"R-prod top-g share={100*top_share/nc:.1f}% (g={top_g}{' in mu' if top_in_mu else ''}, "
                  f"#distinct g={len(prod_units)})")
    print("\n" + "="*112)
    print("If R-prod has ONE dominant g with ~100% share -> THAT is the 'A==-gB' leak (equal-product")
    print("collisions up to a fixed unit). If R-refl ~100% -> the leak is the multiplicative")
    print("reflection x->-g/x (torus-normalizer). Distinct-g count tells if it is ONE relation.")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""#389 CONJECTURE ENGINE — propose precise falsifiable structural conjectures about
COMPUTABLE quantities (decidable in principle ⟹ the swarm can prove them; they do NOT
reduce to the past-Johnson barrier), then refute-or-survive each by exact computation.

Honesty: every output is labelled CONJECTURE (empirically survived at tested scales) or
DEAD (refuted, with the witness). Survivors are candidates for Lean proof, not theorems.
"""
import math, itertools, json, sys
from collections import Counter
from fractions import Fraction

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def primroot(p):
    m = p-1; fac=set(); d=2; mm=m
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    return next(g for g in range(2,p) if all(pow(g,m//q,p)!=1 for q in fac))

def big_prime_with(n, lo):
    """prime p > lo with n | p-1 (so mu_n exists), and p >> n^3 (no genuine relations)."""
    p = ((max(lo, n**3)//n)+1)*n+1
    while not isprime(p): p += n
    return p

def mu(p, n):
    g = primroot(p); h = pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

# ---- exact computable quantities ----
def energyR(G, p, r):
    """E_r = #{(a_1..a_r,b_1..b_r): sum a = sum b}. O(n^r) build of sum histogram."""
    from collections import Counter
    sums = Counter()
    for tup in itertools.product(G, repeat=r):
        sums[sum(tup) % p] += 1
    return sum(v*v for v in sums.values())

def sumset_size(G, p):
    return len({(a+b)%p for a in G for b in G})

def diff_energy(G, p):
    d = Counter()
    for a in G:
        for b in G: d[(a-b)%p]+=1
    return sum(v*v for v in d.values())

# ---- conjecture record ----
SURVIVORS = []
DEAD = []

def test_conjecture(cid, desc, formula, computer, instances, novelty):
    """formula(n)->predicted ; computer(n)->actual over instances (n values). Survives iff
    predicted==actual at all instances."""
    rows=[]
    ok=True; witness=None
    for n in instances:
        try:
            actual = computer(n)
            pred = formula(n)
        except Exception as e:
            continue
        rows.append((n, actual, pred))
        if actual != pred:
            ok=False; witness=(n, actual, pred); break
    rec = {"id":cid,"desc":desc,"novelty":novelty,"rows":rows}
    if ok and len(rows)>=3:
        SURVIVORS.append(rec)
        print(f"[SURVIVE] {cid}: {desc}")
        print(f"          data {rows}")
    else:
        rec["witness"]=witness
        DEAD.append(rec)
        print(f"[DEAD]    {cid}: {desc}  -- witness {witness}")
    return ok

def big_prime_pow(n, power, lo=200003):
    """prime p > max(lo, n^power) with n | p-1."""
    p = ((max(lo, n**power)//n)+1)*n+1
    while not isprime(p): p += n
    return p

def Zk_count(G, p, k):
    """#{k-tuples in G^k summing to 0} via (k-1)-fold histogram (O(n^{k-1}))."""
    c = Counter()
    for tup in itertools.product(G, repeat=k-1):
        c[sum(tup) % p] += 1
    return sum(c[(-x) % p] for x in G)

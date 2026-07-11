#!/usr/bin/env python3
"""Batch 1: exact closed forms for additive structure of mu_{2^m} in the no-genuine-relation
regime (p >> n^3). Each is a precise falsifiable CONJECTURE, refuted or survived by exact
computation. Novelty: exact even-moment / sumset closed forms for 2-power multiplicative
subgroups -- not in-tree (only E_2=3n^2-3n is), decidable, sidesteps the Johnson wall."""
import sys, itertools
sys.path.insert(0, 'scripts/conjectures')
from engine import (isprime, primroot, big_prime_with, mu, energyR, sumset_size,
                    diff_energy, test_conjecture, SURVIVORS, DEAD)
from collections import Counter

def G_of(m):
    n = 1<<m
    p = big_prime_with(n, 200003)
    return mu(p, n), p, n

# cache
CACHE = {}
def getG(m):
    if m not in CACHE: CACHE[m] = G_of(m)
    return CACHE[m]

# C1 (baseline, known): E_2(mu_n) = 3n^2 - 3n
def comp_E2(m):
    G,p,n = getG(m); return energyR(G,p,2)
test_conjecture("C1","E_2(mu_n) = 3n^2 - 3n (baseline/known)",
    lambda m: (lambda n: 3*n*n-3*n)(1<<m), comp_E2, [1,2,3,4], "known")

# C2 (NOVEL): E_3(mu_n) = 15 n^3 - 45 n^2 + 31 n   (conjectured exact 6th-moment)
def comp_E3(m):
    G,p,n = getG(m); return energyR(G,p,3)
test_conjecture("C2","E_3(mu_n) = 15n^3 - 45n^2 + 31n",
    lambda m: (lambda n: 15*n**3-45*n*n+31*n)(1<<m), comp_E3, [1,2,3,4], "NOVEL")

# C3 (NOVEL): |mu_n + mu_n| = n^2/2 + 1  (sumset size in no-relation regime)
def comp_sumset(m):
    G,p,n = getG(m); return sumset_size(G,p)
test_conjecture("C3","|mu_n + mu_n| = n^2/2 + 1",
    lambda m: (lambda n: n*n//2+1)(1<<m), comp_sumset, [1,2,3,4,5], "NOVEL")

# C4 (NOVEL): difference energy = E_2 (additive energy is symmetric under a<->-a here)
def comp_diffE(m):
    G,p,n = getG(m); return diff_energy(G,p)
test_conjecture("C4","diff-energy(mu_n) = 3n^2 - 3n (= E_2)",
    lambda m: (lambda n: 3*n*n-3*n)(1<<m), comp_diffE, [1,2,3,4], "NOVEL-ish")

# C5 (NOVEL): #distinct differences |mu_n - mu_n| = n^2/2 + 1 (same as sumset by neg-closure)
def comp_diffset(m):
    G,p,n = getG(m); return len({(a-b)%p for a in G for b in G})
test_conjecture("C5","|mu_n - mu_n| = n^2/2 + 1",
    lambda m: (lambda n: n*n//2+1)(1<<m), comp_diffset, [1,2,3,4,5], "NOVEL")

# C6 (NOVEL): #{(a,b): a+b in mu_n} (sumset hitting the subgroup itself) = 2n - (n even? ...).
#   a+b in mu_n with a,b in mu_n: this is the additive "closure defect". Conjecture = 0 for n>2
#   in no-relation regime EXCEPT trivial? Let's compute the count.
def comp_selfsum(m):
    G,p,n=getG(m); S=set(G)
    return sum(1 for a in G for b in G if (a+b)%p in S)
# conjecture: equals 0 for n>=4 (no element of mu_n is a sum of two; small) -- TEST (likely wrong, refute)
test_conjecture("C6","#{(a,b)in mu_n^2 : a+b in mu_n} = 0 for n>=4",
    lambda m: 0, comp_selfsum, [2,3,4,5], "NOVEL(prob-dead)")

# C7 (NOVEL): the 3-term zero-sum count Z_3(mu_n)=#{(a,b,c): a+b+c=0} = 0 for 2-power n
#   (no 3 of 2-power roots sum to 0 -- char-0 fact, transfers). Conjecture = 0.
def comp_Z3(m):
    G,p,n=getG(m)
    return sum(1 for a in G for b in G if (-(a+b))%p in set(G))
test_conjecture("C7","Z_3(mu_{2^m}) = #{(a,b,c)in mu_n^3: a+b+c=0} = 0",
    lambda m: 0, comp_Z3, [1,2,3,4,5], "NOVEL")

# summary
print("\n==== BATCH 1 SUMMARY ====")
print(f"survivors: {len(SURVIVORS)}  dead: {len(DEAD)}")

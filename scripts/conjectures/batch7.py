#!/usr/bin/env python3
"""Batch 7: corrected formulas (derived from C12/C13 distribution) + a^2+b^2 structure."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import big_prime_pow, mu, energyR, test_conjecture, SURVIVORS, DEAD
from collections import Counter
def Gp(n,power): p=big_prime_pow(n,power); return mu(p,n),p
# Cd2': Σ_{t≠0} N(t)^2 = 2n^2-3n  (from N-distribution: 4*(n^2-2n)/2 + n)
def diffE_minus(m):
    n=1<<m; G,p=Gp(n,2); d=Counter()
    for a in G:
        for b in G:
            if a!=b: d[(a-b)%p]+=1
    return sum(v*v for v in d.values())
test_conjecture("Cd2","Σ_{t≠0}|μ_n∩(μ_n−t)|² = 2n²−3n",
    lambda m:(lambda n:2*n*n-3*n)(1<<m), diffE_minus, [2,3,4,5],"NOVEL")
# Csd': restricted E_2 (a≠b) = 3n^2-4n
def E2_distinct(m):
    n=1<<m; G,p=Gp(n,2); sums=Counter()
    for a in G:
        for b in G:
            if a!=b: sums[(a+b)%p]+=1
    return sum(v*v for v in sums.values())
test_conjecture("Csd","E_2 restricted to a≠b: Σ_c r'(c)² = 3n²−4n",
    lambda m:(lambda n:3*n*n-4*n)(1<<m), E2_distinct, [2,3,4,5],"NOVEL")
# Csq: #{(a,b)∈μ_n²: a²+b²∈μ_n} = 0
def sq_sum(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for a in G for b in G if (a*a+b*b)%p in S)
test_conjecture("Csq","#{(a,b)∈μ_n²: a²+b²∈μ_n} = 0",
    lambda m:0, sq_sum, [2,3,4,5],"NOVEL")
# Ccube: #{(a,b)∈μ_n²: a³+b³∈μ_n} = 0 (n>=8)
def cube_sum(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for a in G for b in G if (a**3+b**3)%p in S)
test_conjecture("Ccube","#{(a,b)∈μ_n²: a³+b³∈μ_n} = 0",
    lambda m:0, cube_sum, [3,4,5],"NOVEL")
# Cprod: #{(a,b,c)∈μ_n³: a+b = 2c} (midpoint structure) -- conjecture = n (only a=b=c)
def midpoint(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for a in G for b in G if (a+b)*pow(2,p-2,p)%p in S)
pts=[2,3,4,5]; 
print("midpoint #{a+b=2c, c∈μ_n}:", [(1<<m, midpoint(m)) for m in pts])
test_conjecture("Cmid","#{(a,b)∈μ_n²: (a+b)/2 ∈ μ_n} = n (only a=b)",
    lambda m:(1<<m), midpoint, [2,3,4,5],"NOVEL")
print("\n==== BATCH 7 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")

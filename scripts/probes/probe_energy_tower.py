# 2-ADIC TOWER attack on the boundary energy. At p (with n=2^m | p-1), the chain
# μ_2⊂μ_4⊂...⊂μ_n ⊂ F_p. Per-level surplus Δ_j = E(μ_{2^{j+1}}) − 4E(μ_{2^j}) − 6·2^j.
# CHAR-0 prediction: Δ_j = 0. Measure the actual Δ_j at the boundary p≈n²: is Σ_j Δ_j ≤ C·n²·log n?
import sympy
from collections import Counter
import math
def subchain(p, mtop):
    # μ_{2^j} for j=1..mtop in F_p, all coherent (powers of one generator of μ_{2^mtop})
    n=2**mtop; g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)  # generator of μ_n
    subs={}
    for j in range(1,mtop+1):
        nj=2**j
        gen=pow(h, n//nj, p)  # generator of μ_{2^j}
        subs[j]=[pow(gen,t,p) for t in range(nj)]
    return subs
def E2(G,p):
    r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
for mtop in [4,5,6,7]:
    n=2**mtop
    # boundary prime p≈n²
    base=n*n; cand=base-(base%n)+1
    while not sympy.isprime(cand): cand+=n
    p=cand
    subs=subchain(p,mtop)
    Es={j:E2(subs[j],p) for j in subs}
    deltas=[]
    for j in range(1,mtop):
        d=Es[j+1]-4*Es[j]-6*(2**j)
        deltas.append((j, d))
    total_surplus=Es[mtop]-(3*n*n-3*n)
    print(f"n={n} p={p}(≈n^{math.log(p)/math.log(n):.2f}): E(μ_n)={Es[mtop]} char0={3*n*n-3*n} surplus={total_surplus}")
    print(f"   per-level Δ_j (j=1..{mtop-1}): {deltas}")
    print(f"   Σ|Δ_j|={sum(abs(d) for _,d in deltas)}, vs n²={n*n}, n²ln n={n*n*math.log(n):.0f}, max|Δ_j|={max(abs(d) for _,d in deltas)}")

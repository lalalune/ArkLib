"""
A9 probe 1 (FAST): the BAD-GAMMA SET as an additive object -> is PFR / Kelley-Meka non-vacuous?
Band kept small (w=k+1 with k=1 or 2) so C(n,w) is enumerable for n up to 64.
Tests the PFR doubling kill and the KM 3AP-free question on the actual bad-scalar set.
Proper mu_n: p prime, n=2^mu, n|p-1, p>>n^3, NEVER n=p-1.
"""
import math, itertools
from sympy import isprime, primitive_root

def subgroup(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)]

def dd_top(vals,xs,p):
    m=len(xs); tot=0
    for i in range(m):
        d=1
        for j in range(m):
            if j!=i: d=(d*(xs[i]-xs[j]))%p
        tot=(tot+vals[i]*pow(d,-1,p))%p
    return tot

def badset(a,b,k,H,p):
    n=len(H); bad=set(); w=k+1
    for T in itertools.combinations(range(n),w):
        xs=[H[i] for i in T]
        va=[pow(x,a,p) for x in xs]; vb=[pow(x,b,p) for x in xs]
        dA=dd_top(va,xs,p); dB=dd_top(vb,xs,p)
        if dB%p==0: continue
        g=(-dA*pow(dB,-1,p))%p
        if g!=0: bad.add(g)
    return bad

def n3ap(S,p):
    Ss=set(S); c=0
    for x in S:
        for y in S:
            if x!=y and (2*y-x)%p in Ss: c+=1
    return c

def dbl(S,p):
    Sl=list(S); ss=set((x+y)%p for x in Sl for y in Sl); return len(ss),len(ss)/max(1,len(S))

def mult_coset_count(S,n,p):
    """How many mu_n-cosets does S occupy? (the bad set is a union of mu_d cosets; report orbit count)
    orbit of g under <H> : multiply by all of H, see distinct orbits."""
    H=set(subgroup(n,p)); Sl=set(S); seen=set(); orbits=0
    for g in Sl:
        if g in seen: continue
        orbits+=1
        for h in H:
            seen.add((g*h)%p)
    return orbits

print("="*100)
print("A9 probe1 FAST: bad-gamma SET as additive object. PFR vacuous if K^9>=|B|; KM only if 3AP-free.")
print("="*100)
print(" n   k   p          (a,b)  |B|   bud=n |B|<=n 3APfree #3AP  K=dbl/|B| K^9>=|B|? mu_n-orbits alpha")
print("-"*100)
for mu in range(2,6):
    n=2**mu
    k=1 if n<=16 else 2          # small band so C(n,k+1) enumerable
    a,b=k+1,k
    p=n**4-(n**4%n)+1
    while not(isprime(p) and (p-1)%n==0): p+=n
    H=subgroup(n,p)
    B=badset(a,b,k,H,p)
    if not B:
        print(" %-3d %-3d %-10d (%d,%d) EMPTY"%(n,k,p,a,b)); continue
    n3=n3ap(B,p); dc,K=dbl(B,p); orb=mult_coset_count(B,n,p); alpha=len(B)/p
    pfr_vac = (K**9 >= len(B))
    print(" %-3d %-3d %-10d (%d,%d) %-5d %-5d %-6s %-7s %-5d %-9.2f %-9s %-11d %.2e"%(
        n,k,p,a,b,len(B),n,"YES" if len(B)<=n else "no","YES" if n3==0 else "no",
        n3,K,"VACUOUS" if pfr_vac else "useful",orb,alpha))
print()
print("READING: PFR coset-cover is VACUOUS when K^9 >= |B| (>=|B| cosets, no compression).")
print("         #bad/orbit = the count; bad set IS union of mu_d-cosets (group-like, already proven).")

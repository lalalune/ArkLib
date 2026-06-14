import math, sympy
from itertools import product
from collections import defaultdict
# THE GLOBAL DEGREE-BUDGET ARGUMENT (moment-free candidate, directive route 1+3).
# Decompose c by residue mod d: C_r(X)=sum_{l<k, l=r mod d} c_l X^l, r=0..d-1.
# C_r has degree < k, supported on degrees = r mod d, so it has <= ceil((k-r)/d) ~ k/d terms,
# hence as a poly in X^d times X^r: C_r(X) = X^r * Dtilde_r(X^d), deg Dtilde_r < k/d.
# On coset z*mu_d, full-coset agreement <=> C_r(z)=0 for all r != a0:=a mod d, and C_{a0}(z)=w(z).
# PARTIAL agreement on coset z (the directive's ragged core): the per-coset poly
#   Q_z(omega) = sum_{r} omega^{r} C_r(z) - w(z) omega^{a0}     (omega ranges over mu_d)
# has agreement = #{omega in mu_d: Q_z(omega)=0}. The NONZERO terms of Q_z (as a function of
# omega, a poly of degree<d) are at exponents R(z) = {r: C_r(z)!=0} U {a0}. Q_z is m_z-sparse
# with m_z = |R(z)|. By per-coset dichotomy (PROVEN), partial agreement <= m_z - 1.
# m_z <= (#r with C_r != 0) + 1 <= min(d, #nonzero-residues-of-c) + 1.
# GLOBAL: sum over PARTIAL cosets of (agreement) <= sum_z (m_z - 1).
# The single-c constraint: C_r(z)=0 happens for few z (deg C_r < k => <= k-1 roots).
# So "m_z small" (few active frequencies) requires many C_r(z)=0, which is rare.
# Let me MEASURE, at the worst ragged S: the multiset {m_z : partial cosets z} and check
# whether sum (m_z - 1) over partial cosets, which bounds |S|_partial, is <= sqrt(nk)-ish, AND
# whether it's bounded MOMENT-FREELY by k (the degree budget) rather than needing 2nd moment.
def find_w(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def is_coset_union(idx,n,d):
    nod=n//d; S=set(idx); return all((i+nod)%n in S for i in S)
def ragged(idx,n):
    for dd in [d for d in range(2,n+1) if n%d==0]:
        if is_coset_union(idx,n,dd): return False
    return True
def analyze(n,k,p,a,b):
    w=find_w(p,n); d=math.gcd(a-b,n); nod=n//d; J=math.sqrt(n*k); a0=a%d
    mu=[pow(w,i,p) for i in range(n)]
    binv=[pow(pow(x,b,p),p-2,p) for x in mu]; xa=[pow(x,a,p) for x in mu]
    powtab=[[pow(x,j,p) for j in range(k)] for x in mu]
    # coset reps: index cidx=0..nod-1 -> z=w^cidx
    best=None; maxrag=0
    for coeffs in product(range(p),repeat=k):
        groups=defaultdict(list)
        for i in range(n):
            cx=0
            for j in range(k): cx=(cx+coeffs[j]*powtab[i][j])%p
            gamma=((cx-xa[i])*binv[i])%p
            groups[gamma].append(i)
        for gamma,idxs in groups.items():
            if gamma==0 or len(idxs)<2: continue
            if not ragged(idxs,n): continue
            if len(idxs)<=maxrag: continue
            maxrag=len(idxs)
            # compute per-coset m_z and active-frequency structure
            occ=defaultdict(list)
            for i in idxs: occ[i%nod].append(i)
            # for each partial coset rep z, compute C_r(z) and m_z
            info=[]
            for cidx,members in occ.items():
                z=mu[cidx]
                Cr=[0]*d
                for l in range(k):
                    Cr[l%d]=(Cr[l%d]+coeffs[l]*pow(z,l,p))%p
                active=set(r for r in range(d) if Cr[r]!=0)|{a0}
                mz=len(active)
                full = (len(members)==d)
                info.append((len(members),mz,full))
            best=(len(idxs),d,info)
    return d,J,maxrag,best
n=16;p=17
while (p-1)%n or not sympy.isprime(p): p+=1
print("Per-coset frequency-sparsity m_z at the WORST ragged S (n=16,p=17):",flush=True)
for k in [2,3,4]:
    for (a,b) in [(9,5),(13,5)]:
        d=math.gcd(a-b,n)
        if a<=k: continue
        dd,J,mr,best=analyze(n,k,p,a,b)
        if best:
            sz,dd2,info=best
            # bound: sum over partial of (mz-1) >= partial points; check
            partial_bound=sum(mz-1 for (cnt,mz,full) in info if not full)
            partial_actual=sum(cnt for (cnt,mz,full) in info if not full)
            full_pts=sum(cnt for (cnt,mz,full) in info if full)
            print(f" k={k} (a,b)=({a},{b}) d={dd} J={J:.2f} |S|={sz}: per-coset (cnt,m_z,full)={info}",flush=True)
            print(f"     partial_pts_actual={partial_actual} <= sum(m_z-1)={partial_bound} ; full_pts={full_pts}",flush=True)
print("ALLDONE",flush=True)

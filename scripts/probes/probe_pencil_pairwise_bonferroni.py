# Probe: the GENERAL pairwise-bounded-overlap pencil double-count (no common core T).
# Setup: r blocks B_i, each |B_i|=r, all share point 1, punctured C_i = B_i \ {1} size r-1,
# pairwise |C_i ∩ C_j| <= Mpair. Bonferroni lower bound:
#    |union C_i| >= sum|C_i| - sum_{i<j}|C_i ∩ C_j|.
# Since union C_i subset (ground \ {1}) size <= n-1, and using sum_pair <= C(r,2)*Mpair:
#    r(r-1) - C(r,2)*Mpair <= |union| <= n-1.
# This is the general pairwise (Bonferroni) bound the sunflower note flags as a separate open brick
# (no common core T; intersections differ per pair). Confirm on real thin-mu_n dilation pencils.
import itertools, random

def primitive_root(p):
    for g in range(2, p):
        seen=set(); x=1; ok=True
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        if len(seen)==p-1:
            return g
    return None

def Fstar_subgroup(p, n):
    if (p-1)%n!=0: return None
    g=primitive_root(p)
    if g is None: return None
    h=pow(g,(p-1)//n,p)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*h)%p
    if len(set(mu))!=n: return None
    return sorted(set(mu))

def inv(a,p): return pow(a,p-2,p)

random.seed(7)
cases=0; viol=0
for (p,n) in [(17,8),(41,8),(97,8),(193,8),(257,8),(97,16),(193,16),(257,16),(673,16),(769,16),(1153,16)]:
    mu=Fstar_subgroup(p,n)
    if mu is None: continue
    cands=[]
    cands.append(set(mu))  # full subgroup (coset core whole, worst)
    half=Fstar_subgroup(p,n//2)
    if half:
        s=set(half)
        extra=[x for x in mu if x not in s]
        if extra: s.add(extra[0])
        cands.append(s)  # half-coset + straggler (prize worst case)
    for _ in range(3):
        k=random.randint(3,n)
        cands.append(set(random.sample(mu,k)))
    for S in cands:
        S=sorted(S); r=len(S)
        if r<2: continue
        blocks=[]
        for z in S:
            zi=inv(z,p)
            blocks.append(set((zi*x)%p for x in S))
        C=[b-{1} for b in blocks]
        sumC=sum(len(c) for c in C)
        sumpair=0; Mpair=0
        for i in range(r):
            for j in range(i+1,r):
                inter=len(C[i]&C[j]); sumpair+=inter; Mpair=max(Mpair,inter)
        union=set().union(*C) if C else set()
        lhs_bonf=sumC - sumpair
        if not (len(union) >= lhs_bonf):
            viol+=1; print("BONFERRONI VIOL",p,n,r,len(union),lhs_bonf)
        Crr2=r*(r-1)//2
        headline_lhs=r*(r-1) - Crr2*Mpair
        if not (headline_lhs <= n-1):
            viol+=1; print("HEADLINE VIOL",p,n,r,"Mpair",Mpair,"lhs",headline_lhs,"n-1",n-1)
        cases+=1
print("cases=%d violations=%d" % (cases,viol))

import math, sympy
from itertools import product
from collections import Counter, defaultdict
# EXHAUSTIVE maximal-agreement-set enumeration over ALL deg<k codewords c (p^k of them) and all
# gamma!=0 (implicit via grouping). Feasible for small p^k. p=17 keeps it small. n=16,k in {2,3,4}.
def find_w(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def is_coset_union(idx,n,d):
    nod=n//d; S=set(idx); return all((i+nod)%n in S for i in S)
def ragged(idx,n):
    for dd in [d for d in range(2,n+1) if n%d==0]:
        if is_coset_union(idx,n,dd): return False
    return True
def exhaustive(n,k,p,a,b):
    w=find_w(p,n); d=math.gcd(a-b,n); nod=n//d; J=math.sqrt(n*k)
    mu=[pow(w,i,p) for i in range(n)]
    binv=[pow(pow(x,b,p),p-2,p) for x in mu]; xa=[pow(x,a,p) for x in mu]
    powtab=[[pow(x,j,p) for j in range(k)] for x in mu]
    maxrag=0; maxcos=0; cntrag=0; persoset_violation=0
    m_freqs = len(set(l%d for l in range(k)) | {a%d})  # per-coset dichotomy threshold
    for coeffs in product(range(p),repeat=k):
        groups=defaultdict(list)
        for i in range(n):
            cx=0
            for j in range(k): cx=(cx+coeffs[j]*powtab[i][j])%p
            gamma=((cx-xa[i])*binv[i])%p
            groups[gamma].append(i)
        for gamma,idxs in groups.items():
            if gamma==0 or len(idxs)<2: continue
            # per-coset dichotomy check: within each coset, agreement is full(d) or <= m-1
            occ=defaultdict(int)
            for i in idxs: occ[i%nod]+=1
            for cs,cnt in occ.items():
                if cnt!=d and cnt>m_freqs-1:
                    persoset_violation+=1
            if ragged(idxs,n):
                cntrag+=1; maxrag=max(maxrag,len(idxs))
            else:
                maxcos=max(maxcos,len(idxs))
    return d,J,maxrag,maxcos,cntrag,m_freqs,persoset_violation
n=16;p=17
while (p-1)%n or not sympy.isprime(p): p+=1
print(f"EXHAUSTIVE n={n} p={p} (all p^k codewords):")
for k in [2,3,4]:
    for (a,b) in [(9,5),(10,2),(15,13),(11,3)]:
        d=math.gcd(a-b,n)
        if d<2: continue
        dd,J,mr,mc,cr,mf,pv=exhaustive(n,k,p,a,b)
        ratio=mr/J if J>0 else 0
        mark="R-THIN OK" if mr<=J else f"!!! VIOLATION mr={mr}>J={J:.2f}"
        print(f"  k={k} (a,b)=({a},{b}) d={dd} J={J:.3f} maxRAG={mr} ratio={ratio:.3f} maxCos={mc} "
              f"#rag={cr} m={mf} percosetViol={pv}  {mark}",flush=True)
print("ALLDONE",flush=True)

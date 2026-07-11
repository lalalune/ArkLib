# DECISIVE: do spurious (non-coset) gap-valid configs exist ONLY for p < N0 = char-0 |Sigma|?
# If yes, prize regime (p >> N0) has NO spurious configs => coset-saturation holds => lemma vacuous => CLOSED.
import numpy as np
from itertools import combinations
from sympy import primerange

def char0_sigma(n,r):
    HALF=n//2
    vecs=set()
    for W in combinations(range(HALF),r):
        v=[0]*HALF
        for l in W:
            e=(2*l)%n
            if e<HALF: v[e]+=1
            else: v[e-HALF]-=1
        vecs.add(tuple(v))
    return len(vecs)

def spurious_count_at(n,r,p):
    """count gap-valid configs over F_p that are NOT coset-unions (antipodal-symmetric)."""
    HALF=n//2; size=2*r; gap=[1,3]
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    mu=[pow(g,j,p) for j in range(n)]
    # iterate all size-subsets (n<=32 only; for n=64 use sampling)
    from math import comb
    if comb(n,size)>3_000_000: return "too big"
    spur=0; valid=0
    for S in combinations(range(n),size):
        us=[mu[j] for j in S]
        if sum(us)%p!=0: continue
        # e3=0 check
        e3=0
        for c in combinations(us,3): 
            pr=1
            for x in c: pr=pr*x%p
            e3=(e3+pr)%p
        if e3!=0: continue
        valid+=1
        Sset=set(S)
        is_coset = all(((j+HALF)%n) in Sset for j in S)  # antipodal-symmetric
        if not is_coset: spur+=1
    return valid,spur

for (n,r) in [(16,3),(16,4),(32,3)]:
    N0=char0_sigma(n,r)
    print(f"\n=== n={n} r={r}: char-0 N0={N0} ===")
    for p in primerange(n+1, 6*N0):
        if p%n!=1: continue
        res=spurious_count_at(n,r,p)
        if res is None or res=="too big": continue
        v,s=res
        tag = "SATURATED" if p<N0 else "non-sat"
        if s>0 or p<N0+200:   # show all saturated + any spurious
            print(f"  p={p} ({tag}, p/N0={p/N0:.2f}): valid={v}, spurious(non-coset)={s}"
                  + ("  <<< SPURIOUS in NON-SATURATED!" if s>0 and p>N0 else ""))

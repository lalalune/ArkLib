#!/usr/bin/env python3
"""
ODD-EXCESS SPIKE q-DEPENDENCE / THINNESS test (issue #444, OddExcessLaw.lean open core).

Object: full-domain EVEN-direction far-line incidence I_n(x^4) over mu_16 at code degree 4, binding
rung r=10 (delta=0.625, one beyond the half's binding). The in-tree / probe_farline value is 89,
reported as 'p-independent' -- but that was measured ONLY in the THIN regime (p ~ n^4).

QUESTION (rule-3 THINNESS): is I_n(x^4; r=10) = 89 genuinely q-INVARIANT (then the spike is a
fixed cyclotomic number, NOT thinness-essential), or does it DROP as mu_n thickens (q small,
index m=(p-1)/n shrinks)? If it drops with thickness, the spike value 89 is a THIN-regime number
=> the odd-excess spike IS thinness-essential (a genuine prize-direction signal).

We sweep p across a wide index range m = (p-1)/16, from THICK (m small, >=2 to stay PROPER, never
n=q-1) to THIN (m ~ n^3). proper mu_16 always; NEVER n=q-1. Exact, no floats.
"""
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_407_oddexcess_n16_validate import subgroup, incidence

def isprime(m):
    if m<2: return False
    for d in range(2,int(m**0.5)+1):
        if m%d==0: return False
    return True

def In_dir(S, p, K, r, b):
    n=len(S); size=n-r
    if size<=K: return p
    if not (K <= b < size): return None
    best=-1
    for a in range(n):
        if a==b: continue
        c,sat=incidence(S,p,K,a,b,r)
        if sat: c=p
        if c>best: best=c
    return best

if __name__=='__main__':
    n=16; K=4; r=10; b=4
    print(f"I_n(x^{b}) over mu_{n}, code degree {K}, rung r={r} (delta={r/n}); in-tree THIN value = 89")
    print(f"sweep index m=(p-1)/{n} from THICK to THIN (proper mu_{n}, never n=q-1):\n")
    print(f"{'m=(p-1)/n':>10} {'p':>10} {'q/n':>8} {'I_n(x^4;r=10)':>14}")
    print("-"*48)
    # pick representative indices spanning thick -> thin
    targets = [2,3,4,6,10,20,50,150,500,2000,4096]
    seen=set()
    for mt in targets:
        # smallest prime p = n*m+1 with m>=mt
        m=mt
        while True:
            p=n*m+1
            if isprime(p): break
            m+=1
        if p in seen: continue
        seen.add(p)
        S=subgroup(p,n)
        if S is None: print(f"{m:>10} {p:>10}  subgroup fail"); continue
        t=time.time()
        val=In_dir(S,p,K,r,b)
        print(f"{m:>10} {p:>10} {p/n:>8.1f} {val:>14}   ({time.time()-t:.1f}s)", flush=True)

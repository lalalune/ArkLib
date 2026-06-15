#!/usr/bin/env python3
"""
ODD-EXCESS rho-GATE onset: is the SPIKE-ONSET RUNG (not the value) thinness-sensitive? (#444)

Companion to probe_407_oddexcess_qsweep.py (which showed the spike VALUE I_n=89 is thickness-invariant).
The in-tree note (OddExcessLaw.lean) says: E = I_n - I_{n/2} is 0 at every rung BELOW the half binding
rung, then SPIKES at it; and below rho=1/4 (e.g. rho=1/8) E=0 at every rung (rho-GATED). The VALUE is
thin-blind (qsweep). The remaining thinness candidate is the GATE: does the spike turn on at the same
(rung, rho) thin vs thick, or is the ONSET thin-sensitive?

We sweep the full-domain rung r and read where E first becomes > 0, for THIN (p~n^4) and THICK
(beta~2.4) primes, at fixed rho=1/4 (k_full code degree 4, even direction x^4 on mu_16). Exact mod p,
PROPER mu_16, never n=q-1.
"""
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_407_oddexcess_n16_validate import subgroup, incidence

def isprime(m):
    if m<2: return False
    for d in range(2,int(m**0.5)+1):
        if m%d==0: return False
    return True
def In_dir(S,p,K,r,b):
    n=len(S);size=n-r
    if size<=K:return p
    if not(K<=b<size):return None
    best=-1
    for a in range(n):
        if a==b:continue
        c,sat=incidence(S,p,K,a,b,r)
        if sat:c=p
        if c>best:best=c
    return best

if __name__=='__main__':
    n=16; nh=8; K=4; b_even=4; b_half=2; k_half=2
    print(f"E onset across rungs: I_n(x^4)/mu16 deg4 vs I_n/2(x^2)/mu8 deg2, full rung r, half rung r//2")
    print(f"thin p=65537 vs thick p=769(beta~2.4); rho=1/4\n")
    for label,p in [("THIN  p=65537",65537),("THICK p=769 ",769)]:
        Sf=subgroup(p,n); Sh=subgroup(p,nh)
        print(f"--- {label} (idx_full={(p-1)//n}) ---")
        for r in range(K+1, n-K):           # full-domain rungs
            rh = r//2                         # squaring halves the radius
            if rh < k_half+1: 
                Ih=None
            else:
                Ih = In_dir(Sh,p,k_half,rh,b_half)
            In = In_dir(Sf,p,K,r,b_even)
            E = None if (Ih is None or In is None) else In-Ih
            tag = "  <== E>0 ONSET" if (E is not None and E>0) else ""
            print(f"  full r={r:>2} (delta={r/n:.3f}) half rh={rh}: I_n={In} I_n/2={Ih} E={E}{tag}", flush=True)
        print()

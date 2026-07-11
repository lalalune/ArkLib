import sys,time
sys.path.insert(0,'scripts/probes')
from probe_407_oddexcess_n16_validate import subgroup, incidence
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
p=int(sys.argv[1]); label=sys.argv[2]
n=16;nh=8;K=4;b_even=4;b_half=2;k_half=2
Sf=subgroup(p,n); Sh=subgroup(p,nh)
print(f"{label} p={p} idx={(p-1)//n}",flush=True)
for r in (8,9,10):
    rh=r//2
    Ih=In_dir(Sh,p,k_half,rh,b_half) if rh>=k_half+1 else None
    t=time.time(); In=In_dir(Sf,p,K,r,b_even)
    E=None if (Ih is None or In is None) else In-Ih
    print(f"  r={r} (d={r/n:.3f}) rh={rh}: I_n={In} I_n/2={Ih} E={E}  ({time.time()-t:.0f}s)",flush=True)

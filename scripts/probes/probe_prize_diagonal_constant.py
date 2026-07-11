import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, max_period_sq_over_n
import numpy as np

def primes_beta(n, beta, want, used):
    base = int(round(n**beta)); base -= base % n; base += 1
    out=[]; p=base; tries=0
    while len(out)<want and tries<400000:
        if p>3 and is_prime(p) and odd_part((p-1)//n)>1 and p not in used:
            out.append(p); used.add(p)
        p+=n; tries+=1
    return out

print("PRIZE DIAGONAL: beta=4 fixed (m=n^3), C = B/sqrt(n*ln m), multi-prime")
print(f"{'n':>5} {'#pr':>4} {'mean ln m':>10} {'mean C':>9} {'C spread':>16} {'mean C^2(infl)':>13}")
used=set()
for n,want in [(16,5),(32,5),(64,4),(128,3),(256,1)]:
    ps=primes_beta(n,4.0,want,used)
    Cs=[]; lnms=[]
    for p in ps:
        v=max_period_sq_over_n(p,n)   # = max|eta|^2/n
        lnm=math.log((p-1)//n)
        Cs.append(math.sqrt(v/lnm)); lnms.append(lnm)
    Cs=np.array(Cs)
    print(f"{n:>5} {len(ps):>4} {np.mean(lnms):>10.3f} {Cs.mean():>9.3f} "
          f"[{Cs.min():.3f},{Cs.max():.3f}] {(Cs**2).mean():>13.3f}")
print("\nReading: if mean C flat ~const across n => inflated-but-stable constant (form holds, C!=1).")
print("         if mean C grows with n => form at risk. Bare-Gaussian would be C->1.")

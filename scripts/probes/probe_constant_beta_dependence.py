"""#407: is the diagonal inflation C^2 universal or beta-dependent? (sharpens delta* form)"""
import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, max_period_sq_over_n
import numpy as np

def primes_beta(n, beta, want, used):
    base = int(round(n**beta)); base -= base % n; base += 1
    out=[]; p=base; tries=0
    while len(out)<want and tries<600000:
        if p>3 and is_prime(p) and odd_part((p-1)//n)>1 and p not in used:
            out.append(p); used.add(p)
        p+=n; tries+=1
    return out

print("C^2 = (max|eta|^2/n)/ln m along diagonals; n fixed, beta varied")
print("(bare-Gaussian=1; 4th-moment floor=1.5; tests if C^2 grows/falls with beta)")
for n in (32, 64):
    print(f"\n n={n}:  {'beta':>5} {'#pr':>4} {'ln m':>7} {'mean C^2':>9} {'C^2/beta':>9}")
    used=set()
    for beta in (3.0, 3.5, 4.0, 4.5, 5.0):
        ps=primes_beta(n,beta,3,used)
        if not ps: continue
        c2=[]; lnms=[]
        for p in ps:
            v=max_period_sq_over_n(p,n); lnm=math.log((p-1)//n)
            c2.append(v/lnm); lnms.append(lnm)
        c2=np.array(c2)
        print(f"        {beta:>5.1f} {len(ps):>4} {np.mean(lnms):>7.2f} {c2.mean():>9.3f} {c2.mean()/beta:>9.3f}")
print("\nReading: C^2 flat in beta => universal inflation (~1.75); C^2~beta => H(rho)/(beta logn) form self-corrects.")

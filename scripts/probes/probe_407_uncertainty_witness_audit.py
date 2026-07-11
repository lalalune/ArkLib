import math
from math import gcd
exec(open('/tmp/probe_407_maxzeros_sweep.py').read().split('if __name__')[0])
import itertools
k=3; band=list(range(k)); n=32; beta=4.0
p=find_prime(n,beta); w=rou(p,n)
def witness_for_dir(a,b):
    T=band+[a,b]; K=len(T)
    Mfull=[[pow(w,(t*z)%n,p) for t in T] for z in range(n)]
    best=0; bz=None
    for A in itertools.combinations(range(n), K-1):
        c=solve_null([Mfull[z] for z in A],p)
        if c is None: continue
        zl=[z for z in range(n) if sum(Mfull[z][j]*c[j] for j in range(K))%p==0]
        if len(zl)>best: best=len(zl); bz=zl
    return best, bz
for (a,b) in [(17,18),(4,5),(16,18)]:
    s,Z = witness_for_dir(a,b)
    Z=sorted(Z)
    # antipodal structure: is Z closed under z->z+n/2 (antipodal)? is it a coset of a subgroup?
    half=n//2
    antip_closed = all(((z+half)%n in Z) for z in Z)
    # is Z a union of cosets of <2^j>? check stabilizer: largest d|n with Z+ (n/d-shifts) invariant
    # check if Z is invariant under +d for d = n/|subgroup|. Test all divisors.
    coset_struct=[]
    for d in [1,2,4,8,16]:
        if all(((z+d)%n in Z) for z in Z): coset_struct.append(d)
    # differences distribution
    print(f"dir({a},{b}): s*={s}, |Z|={len(Z)}")
    print(f"   Z={Z}")
    print(f"   antipodal-closed (z+n/2 in Z): {antip_closed}")
    print(f"   invariant under shift +d for d in: {coset_struct}  (d=1 => full Z_n; d|n => coset-of-index-d structure)")
    # parity composition
    evens=[z for z in Z if z%2==0]; odds=[z for z in Z if z%2==1]
    print(f"   #even={len(evens)} #odd={len(odds)}")

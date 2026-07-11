import itertools, cmath, math
from collections import Counter
def isprime(k):
    if k<2: return False
    i=2
    while i*i<=k:
        if k%i==0: return False
        i+=1
    return True
def omega(m):  # number of distinct prime factors
    m=abs(m); s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return len(s)
# n=8: Z[zeta_8], zeta^4=-1. root index k -> coeff vector +e_{k%4} if k<4 else -e_{k-4}.
def root_vec(k):
    v=[0,0,0,0]
    if k<4: v[k]=1
    else: v[k-4]=-1
    return v
def norm_zeta8(c):  # field norm N(alpha), alpha=c0+c1 z+c2 z^2+c3 z^3
    prod=1.0
    for j in [1,3,5,7]:
        z=cmath.exp(1j*math.pi*j/4)
        s=c[0]+c[1]*z+c[2]*z**2+c[3]*z**3
        prod*= s
    return round(prod.real)
# Enumerate depth-r relations (a,b), compute alpha = sum(a roots) - sum(b roots) as coeff vector, its norm.
n=8; r=3
phi=4
B=2*r
print(f"n={n} (phi={phi}), depth r={r}.  per-relation bound: omega(N(alpha)) <= phi*log2(2r)={phi*math.log2(2*r):.1f}")
norms=Counter()  # alpha (tuple) -> mult
maxnorm=0; maxomega=0
roots=list(range(n))
# sample to keep it fast: all a-tuples vs all b-tuples is n^{2r}=8^6=262144, fine
for a in itertools.product(roots,repeat=r):
    va=[0,0,0,0]
    for k in a:
        rv=root_vec(k)
        for i in range(4): va[i]+=rv[i]
    for b in itertools.product(roots,repeat=r):
        c=list(va)
        for k in b:
            rv=root_vec(k)
            for i in range(4): c[i]-=rv[i]
        norms[tuple(c)]+=1
# analyze nonzero alpha
nonzero={a:m for a,m in norms.items() if a!=(0,0,0,0)}
mult0=norms[(0,0,0,0)]
print(f"E_r total pairs={sum(norms.values())}, mult(0)=E_char0={mult0}, #distinct nonzero alpha={len(nonzero)}")
omega_ok=True; Nmax=0
for a,m in nonzero.items():
    N=norm_zeta8(a)
    if N==0: continue
    o=omega(N); Nmax=max(Nmax,abs(N))
    if 2**o > B**phi: omega_ok=False
print(f"per-relation bound 2^omega(N) <= B^phi={B**phi} holds for all nonzero alpha? {omega_ok}; max|N|={Nmax}")
# VACUITY check: for a thin prime p, how many distinct nonzero alpha have p | N(alpha)?  (= bad-for-p count)
for p in [4129, 12289]:
    if not (isprime(p) and p%n==1): continue
    badcount=sum(1 for a in nonzero if norm_zeta8(a)!=0 and norm_zeta8(a)%p==0)
    Wr=sum(m for a,m in nonzero.items() if norm_zeta8(a)!=0 and norm_zeta8(a)%p==0)
    print(f"  p={p}: #distinct nonzero alpha with p|N = {badcount}, wraparound contribution Wr={Wr}")
print(f"\nINTERPRETATION (honest):")
print(f"  - per-relation bound 2^omega(N)<=B^phi=(2r)^phi is TIGHT: max|N|={Nmax}=(2r)^phi exactly (archimedean bound achieved).")
print(f"  - thin primes here (p>n^4=4096) EXCEED the norm ceiling max|N|={Nmax}, so W_r=0 (the ONSET CEILING p>(2r)^phi => W=0).")
print(f"  - the many-alpha-per-prime VACUITY regime is p<(2r)^phi; for THIN p that needs r large (the saddle r~log p),")
print(f"    where worst-case W_r = #lattice points of the box in the prime ideal = growing-order equidistribution = the WALL.")
print(f"  => the per-relation bound controls the AVERAGE wraparound; the SUPREMUM (worst prime) is the uncomputable lattice count.")

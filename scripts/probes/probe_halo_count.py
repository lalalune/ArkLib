# Halo = #{(A,B): A,B subset of [0,N), Sum_{j in A} g^j = Sum_{j in B} g^j in F_p}  (incl A=B diagonal)
# = subset-sum ENERGY of {g^0,...,g^{N-1}} = sum_v r(v)^2, r(v)=#{A: sum_{A} g^j = v}.
# Non-antipodal halo = energy - 2^N (remove diagonal A=B). Compare to 4^N/p (equidistribution).
import itertools
def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**.5)+1):
        if p%d==0: return False
    return True
def prim_root_2m(p,m):
    n=2**m
    if (p-1)%n: return None
    for g in range(2,p):
        if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return g
    return None
print(f"{'m':>2}{'N':>4}{'p':>7}{'2^N':>8}{'4^N/p':>10}{'energy':>9}{'halo(E-2^N)':>12}{'halo/(4^N/p)':>13}")
for m in [2,3,4]:
    N=2**(m-1); n=2**m
    for p in [pp for pp in range(n+1, 8000) if is_prime(pp) and (pp-1)%n==0][:3]:
        g=prim_root_2m(p,m)
        if g is None: continue
        pows=[pow(g,j,p) for j in range(N)]
        from collections import Counter
        r=Counter()
        for A in range(2**N):
            s=sum(pows[j] for j in range(N) if (A>>j)&1)%p
            r[s]+=1
        energy=sum(v*v for v in r.values())
        halo=energy-2**N
        approx=4**N/p
        print(f"{m:>2}{N:>4}{p:>7}{2**N:>8}{approx:>10.1f}{energy:>9}{halo:>12}{halo/approx if approx>0 else 0:>13.2f}")

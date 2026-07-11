import sympy
from collections import Counter

def maxrep_nz(H,p):
    cnt=Counter()
    for a in H:
        for b in H:
            s=(a+b)%p
            if s: cnt[s]+=1
    return max(cnt.values()) if cnt else 0

def Hset(p,n):
    g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
    return set(pow(z,j,p) for j in range(n))

print("Rep-bound P_max: largest prime p=1 mod n with max_{c!=0} r(c) > 2. Sweep p from small up.")
for k in (3,4,5):
    n=1<<k
    m=1; lastbad=None; nb=0; cnt=0
    while cnt<6000:
        p=m*n+1; m+=1
        if not sympy.isprime(p) or p<=n+1: continue
        cnt+=1
        if maxrep_nz(Hset(p,n),p)>2:
            lastbad=p; nb+=1
    print(f"n={n}: among first {cnt} primes, #bad(r>2)={nb}, largest bad p={lastbad}, n^4={n**4}, n^3={n**3}")

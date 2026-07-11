import sympy
from collections import Counter

def maxrep_nonzero(H,p):
    cnt=Counter()
    for a in H:
        for b in H:
            s=(a+b)%p
            if s: cnt[s]+=1
    return max(cnt.values()) if cnt else 0

def Hset(p,n):
    g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
    return set(pow(z,j,p) for j in range(n))

print("Sweep MANY primes p~n^4 per n; report any with max_{c!=0} r(c) > 2 (= bad prime, GV fails).")
for k in (3,4,5,6):
    n=1<<k
    base=n**4; m=(base-1)//n
    primes=[]; cnt=0
    while len(primes)<80 and cnt<200000:
        p=m*n+1; m+=1; cnt+=1
        if sympy.isprime(p): primes.append(p)
    bad=[]
    for p in primes:
        mr=maxrep_nonzero(Hset(p,n),p)
        if mr>2: bad.append((p,mr))
    print(f"n={n}: swept {len(primes)} primes ~n^4; #bad (r>2)={len(bad)}; worst={max((b[1] for b in bad),default=2)}; examples={bad[:3]}")

import math
from itertools import combinations, product

def is_prime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
def prim_root(n,p):
    for g in range(2,p):
        if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return g
    return None
def true_min_l1(d,p,g,wmax=20):
    gp=[pow(g,k,p) for k in range(d)]
    for w in range(2, wmax+1):
        for ss in range(1, min(w,d)+1):
            for supp in combinations(range(d), ss):
                for cut in combinations(range(1,w), ss-1):
                    parts=[];prev=0
                    for c_ in cut: parts.append(c_-prev);prev=c_
                    parts.append(w-prev)
                    for signs in product([1,-1],repeat=ss):
                        if sum(signs[i]*parts[i]*gp[supp[i]] for i in range(ss))%p==0:
                            return w
    return None

# n=4 (d=2): cheap, can push p large and see min_l1 ~ p^{1/2}? (Minkowski l1 for d=2 lattice det p)
n=4; d=2
print(f"n={n}, d={d}: min_l1 scaling at generic thin primes (expect ~ p^(1/d)=sqrt(p) scale)")
print("p          v2  min_l1  p^(1/2)  log_n(p)")
import random; random.seed(3)
for target in [10**4, 10**5, 10**6, 10**7]:
    p=target
    found=0
    while found<2 and p<target*2:
        if is_prime(p) and p%n==1:
            v2=0;m=p-1
            while m%2==0:v2+=1;m//=2
            if v2<=3:
                g=prim_root(n,p)
                w=true_min_l1(d,p,g,wmax=2000)
                print(f"{p:<10} {v2:<3} {str(w):<7} {p**0.5:<8.1f} {math.log(p)/math.log(n):<.2f}")
                found+=1
        p+=1

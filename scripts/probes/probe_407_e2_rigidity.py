import itertools
from sympy import primerange, primitive_root, isprime

def roots(n,p,g): return [pow(g,j,p) for j in range(n)]

def count_e2_K(n, p, w, restrict_w=None):
    g = pow(primitive_root(p), (p-1)//n, p)
    mu = roots(n,p,g); muset=set(mu)
    e1vals=[]; cnt=0
    ws = [w] if w is not None else range(2,n+1)
    for k in ws:
        for S in itertools.combinations(mu, k):
            e1 = sum(S)%p
            if e1==0: continue
            p2 = sum((x*x)%p for x in S)%p
            if (e1*e1-p2)%p==0:
                cnt+=1; e1vals.append(e1)
    # orbit count under dilation by mu_n (e1 -> u*e1, u in mu)
    rem=set(e1vals); K=0
    while rem:
        x=next(iter(rem)); rem -= set((u*x)%p for u in mu); K+=1
    return cnt, len(set(e1vals)), K

# For n=16, sweep p in prize-ish growing range, at extremal width w=n/2=8, track K (orbit count of e1)
n=16; h=n//2
print(f"=== n={n}, extremal width w={h}: K (e1-dilation-orbit count) vs growing p ===")
ps=[]
p=n+1
while len(ps)<14:
    if (p-1)%n==0 and isprime(p): ps.append(p)
    p+=1
# include some larger ones in prize-ratio territory
for big in [4099, 16001, 65537, 1048609, 16777249]:
    q=big
    while not((q-1)%n==0 and isprime(q)): q+=1
    ps.append(q)
for p in sorted(set(ps)):
    beta = (p).bit_length()/ (n.bit_length()-1) if n>1 else 0
    import math
    b=math.log(p)/math.log(n)
    cnt,distinct,K = count_e2_K(n,p,h)
    print(f"  p={p:9d} beta={b:.2f} p/n^3={p/n**3:7.1f}: count_w8={cnt:5d} #distinct_e1={distinct:4d} K={K}")

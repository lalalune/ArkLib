import itertools
from collections import Counter

def reduced(counts, n):
    m = n//2
    return tuple(counts[j] - counts[j+m] for j in range(m))

def char0_energy(n, r):
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        counts = [0]*n
        for k in x: counts[k]+=1
        cnt[reduced(counts, n)] += 1
    return sum(v*v for v in cnt.values())

def charp_energy(n, r, p, g):
    roots = [pow(g,k,p) for k in range(n)]
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        s = sum(roots[k] for k in x) % p
        cnt[s]+=1
    return sum(v*v for v in cnt.values())

def order(h,p):
    o=1; x=h%p
    while x!=1:
        x=x*h%p; o+=1
        if o>p: return -1
    return o

def prim_root_order_n(n,p):
    assert (p-1)%n==0
    e=(p-1)//n
    for a in range(2,p):
        h=pow(a,e,p)
        if order(h,p)==n: return h
    return None

def primes_mod(n, count):
    res=[]; p=n+1
    while len(res)<count:
        if p%n==1 and all(p%q for q in range(2,int(p**.5)+1)) and p>2:
            res.append(p)
        p+=1
    return res

n=8; rmax=4
E0={r:char0_energy(n,r) for r in range(1,rmax+1)}
print("n=8 char0 E_r:",E0, " (E2 should be 3*64-24=168)")
primes=primes_mod(n,10)
print("primes:",primes)
for p in primes:
    g=prim_root_order_n(n,p)
    if g is None: continue
    Ep={r:charp_energy(n,r,p,g) for r in range(1,rmax+1)}
    W={r:Ep[r]-E0[r] for r in range(1,rmax+1)}
    dW={r:W[r+1]-n*W[r] for r in range(1,rmax)}
    print(f"p={p}: W={W}")
    for r in range(1,rmax):
        tgt=2*r*n*W[r]; tens=n*n*W[r]
        s1="ok" if (W[r]>0 and dW[r]<=tgt) else ("vac" if W[r]==0 else "VIOL")
        s2="ok" if (W[r]>0 and W[r+1]<=tens) else ("vac" if W[r]==0 else "VIOL")
        print(f"   r={r}: W_r={W[r]} dW={dW[r]} 2rnW_r={tgt}[{s1}] | W_{{r+1}}={W[r+1]} n^2 W_r={tens}[{s2}]")

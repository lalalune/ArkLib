import itertools
def subgroup(p, n):
    # mu_n = n-th roots of unity in F_p^*, requires n | p-1
    assert (p-1) % n == 0
    g = None
    for cand in range(2, p):
        # find element of order exactly n
        if pow(cand, n, p) == 1 and all(pow(cand, n//q, p)!=1 for q in set(prime_factors(n))):
            g = cand; break
    assert g is not None, (p,n)
    return [pow(g, i, p) for i in range(n)]
def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def E_r(G, p, r):
    # count tuples (a_1..a_r, b_1..b_r) in G^{2r} with sum a = sum b mod p
    # = sum over t of N(t)^2 where N(t)=#{r-tuples summing to t}
    from collections import Counter
    cnt = Counter()
    for combo in itertools.product(G, repeat=r):
        cnt[sum(combo)%p]+=1
    return sum(v*v for v in cnt.values())
def is_prime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
import math
print(f"{'p':>7} {'n':>4} {'m':>6} {'E3':>10} {'Wick=15n^3':>12} {'ratio':>7}")
for n in [8,16,32]:
    # find primes p == 1 mod n, p >> n^3 (thin), multiple
    found=0
    for m in range(2, 100000):
        p = m*n+1
        if not is_prime(p): continue
        if p < n**3: continue  # thin: q >> n^3
        try: G=subgroup(p,n)
        except: continue
        e3=E_r(G,p,3)
        wick=15*n**3
        print(f"{p:>7} {n:>4} {(p-1)//n:>6} {e3:>10} {wick:>12} {e3/wick:>7.3f}")
        found+=1
        if found>=3: break

# Find the exact threshold: for which p (with n|p-1, n=2^m) is maxrep(μ_n) ≤ 2?
# Test many primes p≡1 mod n across ranges; record min p with maxrep≤2 and behavior.
import sympy
def subgroup(n, p):
    g = sympy.primitive_root(p); h = pow(g, (p-1)//n, p)
    return set(pow(h, j, p) for j in range(n))
def maxrep(G, p):
    from collections import Counter
    Gs=G
    r = Counter()
    for a in Gs:
        for b in Gs:
            if a!=b: r[(a-b)%p]+=1
    return max((v for t,v in r.items() if t!=0), default=0)
for m in range(2,8):
    n=2**m
    rows=[]
    # sample primes p≡1 mod n from ~n up to ~n^3.5
    cnt=0
    cand=n+1
    while cand < max(n**3*3, 5000) and cnt<60:
        if sympy.isprime(cand):
            G=subgroup(n,cand); mr=maxrep(G,cand)
            rows.append((cand,mr)); cnt+=1
        cand+=n
    # find smallest p where ALL larger sampled p have maxrep≤2
    # report: ratio p/n^k at the last p with maxrep>2
    bad=[p for p,mr in rows if mr>2]
    allp=[p for p,mr in rows]
    if bad:
        last_bad=max(bad)
        import math
        kexp = math.log(last_bad)/math.log(n)
        print(f"n={n}: last p with maxrep>2 is {last_bad} = n^{kexp:.2f}; "
              f"max maxrep over sample={max(mr for _,mr in rows)}; "
              f"#primes sampled={len(rows)} up to {max(allp)}=n^{math.log(max(allp))/math.log(n):.2f}")
    else:
        print(f"n={n}: maxrep≤2 for ALL sampled primes (min={min(allp)}=n^{math.log(min(allp))/math.log(n):.2f})")

# WHEN does repCount(c) >= 3 occur? Mechanism hunt.
# r(c) >= 3 means >= 3 reps c = g1+g2 with gi in mu_n. Equivalently c-g in mu_n for >=3 values g in mu_n.
# i.e. |mu_n cap (c - mu_n)| >= 3. Two distinct n-th roots of unity sets intersecting in >=3 points.
# CLAIM to test: a coincidence c=g1+g2=g1'+g2'=g1''+g2'' forces a NONTRIVIAL ADDITIVE RELATION
# among <=6 n-th roots of unity. Over Q (char 0) such relations are constrained (vanishing sums of
# roots of unity = union of full p-orbits, p prime | n). Over F_p, the relation can hold mod p
# WITHOUT holding over Z -> needs p | (some fixed nonzero integer determined by n).
# So: r(c)>=3 should require p | D_n for some integer D_n depending only on n (a "bad prime" set).
# TEST: for each n, scan ALL primes p = 1 mod n up to some bound; record which have max_c r(c) >= 3.
# If the bad primes are FINITE / all <= poly(n), that's the threshold mechanism.
def order_subgroup(p, n):
    def is_gen(g):
        x=1; 
        for _ in range(p-2):
            x=(x*g)%p
            if x==1: return False
        return True
    g=2
    while not is_gen(g): g+=1
    h=pow(g,(p-1)//n,p)
    return sorted(set(pow(h,j,p) for j in range(n)))
def maxrep(p,n):
    mu=order_subgroup(p,n)
    from collections import Counter
    r=Counter()
    for g1 in mu:
        for g2 in mu:
            c=(g1+g2)%p
            if c!=0: r[c]+=1
    return max(r.values()) if r else 0
import sympy
for n in (4,8,16):
    bad=[]
    cnt=0
    p=n+1
    while cnt<60:
        if (p-1)%n==0 and sympy.isprime(p) and p!=n+1*0+ (n+1 if False else -1) and p-1!=n:
            cnt+=1
            m=maxrep(p,n)
            if m>=3: bad.append((p,m))
        p+=1
    print(f"n={n:2d}: scanned {cnt} primes p=1 mod n; BAD (maxrep>=3): {bad[:25]}")
    if bad:
        maxbad=max(b[0] for b in bad)
        print(f"        largest bad prime = {maxbad}, n^3={n**3}, n^2={n**2}; bad>n^3: {[b for b in bad if b[0]>n**3]}")

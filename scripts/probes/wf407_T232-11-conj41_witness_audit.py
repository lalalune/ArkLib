#!/usr/bin/env python3
"""
wf407_T232-11-conj41_witness_audit.py
=====================================
Audit the n=28 / n=32 mu_n witness that REFUTES the INTENDED (rank/dichotomy,
fixed-syndrome) form of Conjecture 41 -- confirm the supports really are
distinct GENUINE list elements at ONE fixed syndrome, not a counting artifact.

A genuine fixed-syndrome list of size M means: M weight-w supports E_1..E_M, all
sharing the SAME full class (e_1..e_c)(E_i) = same value, with ALL Vandermonde
error values nonzero -> by the O44/O45 decoupling each E_i is compatible with the
SAME syndrome s (the class syndrome) on the SAME line parameter, hence each gives
a DISTINCT codeword in the list at that syndrome.  We verify, exactly over F_p:
  (a) all M supports are pairwise distinct subsets of mu_n;
  (b) all share e_1..e_c (full class);
  (c) every support's locator-derivative error values are all nonzero (genuine);
  (d) the M supports give M distinct error-locator polynomials (=> distinct list
      elements) -- automatic since distinct supports, but we double check loc coeffs;
  (e) the actual codimension-c compatibility CompatC(s,c,E_i) holds at the explicit
      class syndrome s built from the class (Newton e/h), for ALL i simultaneously.
This pins the refutation of the intended form at the M_true level (genuine codewords).
"""

import itertools
from collections import defaultdict

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def nextprime(n):
    n = int(n)+1
    while not is_prime(n): n += 1
    return n

def factorize(n):
    fac={}; d=2
    while d*d<=n:
        while n%d==0: fac[d]=fac.get(d,0)+1; n//=d
        d += 1 if d==2 else 2
    if n>1: fac[n]=fac.get(n,0)+1
    return fac

def primitive_root(p):
    phi=p-1; fac=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    raise RuntimeError

def prize_prime(n):
    p = nextprime(max(n**4,1009))
    while (p-1)%n != 0: p = nextprime(p)
    return p

def mu_n(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p)%p for i in range(n)]

def esymm(E,j,p):
    if j==0: return 1
    acc=0
    for c in itertools.combinations(E,j):
        pr=1
        for x in c: pr=pr*x%p
        acc=(acc+pr)%p
    return acc

def locator_coeffs(E,p):
    co=[1]
    for a in E:
        a%=p; new=[0]*(len(co)+1)
        for i,ci in enumerate(co):
            new[i]=(new[i]-a*ci)%p; new[i+1]=(new[i+1]+ci)%p
        co=new
    return co

def err_vals_nonzero(E,p):
    El=list(E)
    for x in El:
        pr=1
        for y in El:
            if y==x: continue
            d=(x-y)%p
            if d==0: return False
            pr=pr*d%p
        if pr==0: return False
    return True

def full_class_key(E,c,p):
    return tuple(esymm(E,j,p) for j in range(1,c+1))

def synd(s,N,coeffs,p):
    return sum((coeffs[j] if j<len(coeffs) else 0)*s[j] for j in range(N))%p

def syndr_value(E,r,s,N,p):
    base=locator_coeffs(E,p); coeffs=[0]*r+base
    return synd(s,N,coeffs,p)

def complete_homog(class_e, c, p):
    """h_0..h_c from e_1..e_c via Newton: h_m = sum_{i=1..m} (-1)^{i-1} e_i h_{m-i}."""
    e=[1]+[class_e[i] for i in range(c)]  # e[0]=1=e_0, e[i]=e_i
    h=[1]
    for m in range(1,c+1):
        acc=0
        for i in range(1,m+1):
            sign = 1 if (i-1)%2==0 else -1
            acc=(acc + sign*e[i]*h[m-i])%p
        h.append(acc%p)
    return h  # length c+1: h_0..h_c

def class_syndrome(class_e, w, c, p):
    """s1 of length N=w+c with s1 = (0,...,0, h_0, h_1, ..., h_c) placed so that
    CompatC(s1,c,E) <=> e_1..e_c(E)=class.  Layout (O42/O43): zeros in positions
    0..w-1, then h_0..h_c in positions w-1.. ? We instead VERIFY by direct compat,
    using the construction: s1[j] = h_{j-(N-1-c)} for j in [N-1-c, N-1], else 0,
    with N=w+c.  This is the (0..0,h_0..h_c) top-window syndrome of O43."""
    N=w+c
    h=complete_homog(class_e,c,p)  # h_0..h_c
    s=[0]*N
    # place h_0..h_c at the top c+1 positions N-1-c .. N-1
    for t in range(c+1):
        s[N-1-c+t]=h[t]%p
    return s

def banner(t): print("\n"+"="*78); print(t); print("="*78)

def audit(n, w, c):
    banner(f"WITNESS AUDIT  mu_n,  n={n}, w={w}, c={c}   (ceiling floor((2D-1)/c)={(2*(w+c)-1)//c})")
    p=prize_prime(n); L=mu_n(n,p); N=w+c
    print(f"  prime p = {p}   (p-1 mod n = {(p-1)%n}),   |mu_n| = {len(set(L))}")
    # group genuine supports by FULL class
    cls=defaultdict(list)
    for E in itertools.combinations(L,w):
        if err_vals_nonzero(E,p):
            cls[full_class_key(E,c,p)].append(E)
    # worst full class
    key=max(cls,key=lambda k:len(cls[k]))
    fam=cls[key]
    print(f"  worst FULL-class (e_1..e_{c}) = {key}")
    print(f"  list size M_fixed (genuine supports sharing full class) = {len(fam)}")
    # (a) pairwise distinct
    distinct = len(set(fam))==len(fam)
    # (b) all share e_1..e_c
    share = all(full_class_key(E,c,p)==key for E in fam)
    # (c) all genuine
    genuine = all(err_vals_nonzero(E,p) for E in fam)
    # (d) distinct locator polys
    locs = set(tuple(locator_coeffs(E,p)) for E in fam)
    distinct_locs = len(locs)==len(fam)
    # (e) all compatible with the explicit class syndrome simultaneously
    s = class_syndrome(key, w, c, p)
    compat_all = all(all(syndr_value(E,r,s,N,p)==0 for r in range(c)) for E in fam)
    print(f"  (a) pairwise-distinct supports         : {distinct}")
    print(f"  (b) all share full class e_1..e_{c}     : {share}")
    print(f"  (c) all genuine (error values nonzero) : {genuine}")
    print(f"  (d) {len(fam)} distinct error-locator polys : {distinct_locs}")
    print(f"  (e) ALL compatible w/ explicit class syndrome s simultaneously: {compat_all}")
    ceil=(2*N-1)//c
    verdict = "REFUTES intended form" if (len(fam)>ceil and distinct and share and genuine and distinct_locs and compat_all) else \
              ("within ceiling" if len(fam)<=ceil else "AUDIT FAIL (not all genuine/compat)")
    print(f"  => M_fixed={len(fam)} vs ceiling {ceil}:  {verdict}")
    # show the supports as exponent sets in mu_n (i.e. which roots of unity)
    expo = {L[i]:i for i in range(n)}
    print(f"  supports as mu_n-exponent sets:")
    for E in fam[:8]:
        print(f"    {sorted(expo[x] for x in E)}")
    return len(fam), ceil, (distinct and share and genuine and distinct_locs and compat_all)

if __name__ == "__main__":
    print("Audit: does the mu_n M_fixed list genuinely refute the INTENDED (fixed-syndrome)")
    print("rank/dichotomy form of Conjecture 41 at the M_true (genuine codeword) level?\n")
    for n in [24, 28, 32]:
        audit(n, w=6, c=3)
    print("\nDONE.")

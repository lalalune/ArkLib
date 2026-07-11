#!/usr/bin/env python3
"""
wf407_T232-11-conj41_coset_law.py
=================================
Pin the MECHANISM of the mu_n refutation of Conjecture 41's intended form:
the worst fixed-syndrome list size M_fixed(mu_n, w=6, c=3) follows a CLEAN coset
law and welds onto the SAME wall as the esymm-fiber / PTE / Katz-floor n/4 object.

From the witness audit, the worst-class supports at n look like translates with
e_3 = 0.  We:
  (1) confirm M_fixed = floor(n/4) - [n in some residue] : measure the exact law
      for n in {8,12,16,20,24,28,32,36,40} (w=6,c=3);
  (2) decode the support structure: are the M supports a single mu_d-coset orbit
      (Katz floor n/4 / 400-T04 #orbits = n/4-1), confirming the weld;
  (3) cross-check field-independence (char-0 integer vs F_p) -- the prize wall is
      field-independent only if the count is the same in char 0.
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
    n=int(n)+1
    while not is_prime(n): n+=1
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
    p=nextprime(max(n**4,1009))
    while (p-1)%n!=0: p=nextprime(p)
    return p

def mu_n(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p)%p for i in range(n)], h

def esymm(E,j,p):
    if j==0: return 1
    acc=0
    for c in itertools.combinations(E,j):
        pr=1
        for x in c: pr=pr*x%p
        acc=(acc+pr)%p
    return acc

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

def banner(t): print("\n"+"="*78); print(t); print("="*78)

def measure_law(ns, w, c):
    import sys
    banner(f"COSET LAW  M_fixed(mu_n, w={w}, c={c})  vs  floor(n/4)-1  and  n/4")
    ceil=(2*(w+c)-1)//c
    print(f"  ceiling floor((2D-1)/c)={ceil};   conjectured law M_fixed ~ floor(n/4)-1")
    print(f"  {'n':>4} {'p':>11} {'M_fixed':>8} {'n/4-1':>6} {'floor(n/4)':>11} {'>ceil':>6}")
    for n in ns:
        if n<w: continue
        p=prize_prime(n); L,h=mu_n(n,p)
        counts=defaultdict(int)   # only count, don't store families (memory)
        for E in itertools.combinations(L,w):
            if err_vals_nonzero(E,p):
                counts[tuple(esymm(E,j,p) for j in range(1,c+1))]+=1
        M=max(counts.values()) if counts else 0
        print(f"  {n:>4} {p:>11} {M:>8} {n//4-1:>6} {n//4:>11} {('YES' if M>ceil else 'no'):>6}")
        sys.stdout.flush()

def decode_structure(n, w, c):
    banner(f"STRUCTURE DECODE  worst fixed-syndrome family on mu_n  (n={n}, w={w}, c={c})")
    p=prize_prime(n); L,h=mu_n(n,p); expo={L[i]:i for i in range(n)}
    cls=defaultdict(list)
    for E in itertools.combinations(L,w):
        if err_vals_nonzero(E,p):
            cls[tuple(esymm(E,j,p) for j in range(1,c+1))].append(E)
    key=max(cls,key=lambda k:len(cls[k]))
    fam=cls[key]
    print(f"  worst class (e_1..e_{c}) = {key},  M_fixed = {len(fam)}")
    exps=[tuple(sorted(expo[x] for x in E)) for E in fam]
    for e in exps: print(f"    exps {list(e)}")
    # difference structure: subtract min exponent (mod n) from each support
    print("  normalized (subtract first exponent mod n):")
    norm=set()
    for e in exps:
        base=e[0]
        norm.add(tuple(sorted((x-base)%n for x in e)))
    for nz in sorted(norm): print(f"    {list(nz)}")
    print(f"  distinct normalized shapes: {len(norm)} (=1 means a single rotation orbit)")
    # e_c = 0 for all?
    allz = all(esymm(E,c,p)==0 for E in fam)
    print(f"  e_{c} = 0 for the whole family: {allz}  (=> supports are zero-e_{c} = sum/PTE structure)")

def char0_check(n, w, c):
    """char-0: build mu_n as exact complex roots of unity? Instead use exact integer
    surrogate is impossible for roots of unity; verify field-independence by re-running
    over a SECOND, differently-shaped prime and confirming the SAME M_fixed."""
    banner(f"FIELD-INDEPENDENCE  M_fixed over two different primes (n={n}, w={w}, c={c})")
    res=[]
    p=prize_prime(n)
    for which in range(2):
        L,h=mu_n(n,p)
        cls=defaultdict(list)
        for E in itertools.combinations(L,w):
            if err_vals_nonzero(E,p):
                cls[tuple(esymm(E,j,p) for j in range(1,c+1))].append(E)
        key=max(cls,key=lambda k:len(cls[k]))
        res.append((p,len(cls[key])))
        # next prime = 1 mod n, larger
        p=nextprime(p)
        while (p-1)%n!=0: p=nextprime(p)
    for pp,M in res: print(f"    p={pp}: M_fixed={M}")
    print(f"  field-independent: {res[0][1]==res[1][1]}")

if __name__ == "__main__":
    print("Pin the mechanism: M_fixed(mu_n) coset law + weld to Katz-floor/PTE wall.\n")
    measure_law([8,12,16,20,24,28,32,36], w=6, c=3)
    decode_structure(28, w=6, c=3)
    decode_structure(32, w=6, c=3)
    char0_check(28, w=6, c=3)
    char0_check(32, w=6, c=3)
    print("\nDONE.")

#!/usr/bin/env python3
"""LANE wf-M1 SHARP: At a FIXED prize prime p (=1 mod n, p~n^4), count antipodal-free subsets T
of weight w<=2r with p|N(T) -- i.e. the SPURIOUS char-p energy contribution at depth w.
Compare to the char-0 count (antipodal matchings) C0(w)=(w-1)!! * (#pairs choices).
The sufficient lemma needs: spurious(w) <= (small) * C0(w), so E_r^{charp} <= C * E_r^{char0}.

Directly: count T (subset-sum form, weight w, antipodal-free, contains 0) with
sum_{j in T} w_p^{a j} == 0 mod p for SOME odd a  (equivalently p | N(T)).
We use the actual subgroup root w_p mod p and check ALL odd a (= all conjugates)."""
import itertools

def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
def find_p(n,beta):
    base=n**beta; p=base+((1-base)%n)
    while not (p>n and (p-1)%n==0 and isprime(p)): p+=n
    return p
def proot(p):
    x=p-1; f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in f): return a
def antipodal_free(T,n):
    s=set(T); h=n//2
    return all((j+h)%n not in s for j in T)

for n in [16,32,64]:
    p=find_p(n,4); g=proot(p); w=pow(g,(p-1)//n,p)
    print(f"\n=== n={n} p={p} (p~n^4={n**4}, p mod n={p%n}) ===",flush=True)
    # precompute powers table w^{a*j} for odd a, j in 0..n-1
    pw=[[pow(w,(a*j)%n,p) for j in range(n)] for a in range(n)]
    for wt in range(2,9,2):
        spur=0; total_af=0; sampled=0
        for c in itertools.combinations(range(1,n),wt-1):
            T=(0,)+c
            if not antipodal_free(T,n): continue
            total_af+=1; sampled+=1
            hit=False
            for a in range(1,n,2):
                s=0
                tab=pw[a]
                for j in T: s+=tab[j]
                if s%p==0: hit=True; break
            if hit: spur+=1
            if sampled>=400000: break
        # char-0 count at this weight: antipodal-free => 0 over Z, so char-0 spurious=0 by definition.
        # The point: ANY hit here is a PURE char-p spurious (not present over Z).
        print(f"  w={wt}: antipodal-free T checked={total_af}  SPURIOUS(p|N)={spur}  rate={spur/max(1,total_af):.2e}",flush=True)

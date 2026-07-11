# Probe: pigeonhole existence of a short ideal element.
# Generators ±g^k (k<d) act on Z/p. A "word" of length w is a function
# f: Fin w -> {generators} giving a residue sum_i s_i in Z/p.
# Map: weight-<=w signed coefficient vectors c (l1Norm c <= w) -> residue sum_k c_k g^k mod p.
# If #(distinct coeff vectors with l1<=w) > p, two map to same residue =>
#   their DIFFERENCE is a nonzero c' with sum c'_k g^k == 0 mod p (in 0p),
#   and l1Norm(c') <= l1Norm(c1)+l1Norm(c2) <= 2w.
# So: #{c : l1Norm c <= w} > p  =>  exists nonzero c' in ideal with l1 <= 2w.
# We verify the COUNT of weight-<=w vectors and that the forced witness lands.

import itertools, sympy
from collections import defaultdict

def primitive_nth_root(n,p):
    g0=int(sympy.primitive_root(p)); return pow(g0,(p-1)//n,p)

def num_l1_le(d,w):
    # number of integer vectors in Z^d with sum|c_k| <= w
    # = sum_{t=0}^{w} (number with l1 exactly t) ; closed form: sum_{j} C(d,j)C(w,j)2^j  (l1<=w)
    from math import comb
    tot=0
    for t in range(0,w+1):
        # vectors with l1 exactly t: sum_{j=1}^{min(d,t)} C(d,j)*C(t-1,j-1)*2^j ; plus t=0 ->1
        if t==0: tot+=1; continue
        s=0
        for j in range(1,min(d,t)+1):
            s+=comb(d,j)*comb(t-1,j-1)*(2**j)
        tot+=s
    return tot

print("n   d   p        w  #{l1<=w}    p     count>p?  forced-witness-l1<=2w-found?")
for (n,p) in [(8, 17),(8,41),(16,97),(16,193),(32,193),(32,257),(16, 65537)]:
    d=n//2
    if (p-1)%n!=0: 
        # find a prime p ≡1 mod n near
        continue
    g=primitive_nth_root(n,p)
    gp=[pow(g,k,p) for k in range(d)]
    # find smallest w where #{l1<=w} > p
    w=1
    while num_l1_le(d,w)<=p and w<2*d: w+=1
    cnt=num_l1_le(d,w)
    # brute search a forced collision: enumerate coeff vectors l1<=w, hash residue
    seen={}
    found=None
    # enumerate by building from steps to keep feasible: BFS over residue with min-rep coeff
    # We'll just enumerate signed-support combos up to weight w for small d.
    def gen(d,w):
        # yield coeff vectors with l1<=w (as tuples), small only
        if d*1>14 or w>6:
            return
        rng=range(-w,w+1)
        for c in itertools.product(rng,repeat=d):
            if sum(abs(x) for x in c)<=w:
                yield c
    if d<=7 and w<=5:
        for c in gen(d,w):
            r=sum(c[k]*gp[k] for k in range(d))%p
            if r in seen:
                c2=seen[r]
                diff=tuple(c[k]-c2[k] for k in range(d))
                if any(diff):
                    l1=sum(abs(x) for x in diff)
                    found=l1
                    break
            else:
                seen[r]=c
    print(f"{n:<3} {d:<3} {p:<8} {w:<2} {cnt:<11} {p:<6} {str(cnt>p):<8} {found if found else 'n/a(too big)'}")

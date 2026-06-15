#!/usr/bin/env python3
"""Diagnostic: WHY Mann/antipodal undercounts the char-0 agreement count.
   (1) Confirm agreement sets are linear-algebra realizable (g has k free coeffs => any small
       R can be an agreement set), so Mann (fixed +-1 coeffs) is the WRONG governing theorem.
   (2) q-stability of I0 across two big primes (char-0 faithfulness sanity).
   (3) The EXACT-match rows: are they the trivial w>=n-k+? near-Singleton regime?
"""
import itertools
from sympy import isprime

def big_prime(n, lo):
    q = ((lo // n) + 1) * n + 1
    while not isprime(q): q += n
    return q
def gen_mu(q, n):
    for x in range(2, q):
        if pow(x, n, q) == 1 and pow(x, n // 2, q) != 1:
            return [pow(x, i, q) for i in range(n)]
def _rref(rows, p):
    rows=[r[:] for r in rows]; m=len(rows); nc=len(rows[0]) if m else 0; pr=0
    for c in range(nc):
        sel=next((r for r in range(pr,m) if rows[r][c]%p),None)
        if sel is None: continue
        rows[pr],rows[sel]=rows[sel],rows[pr]
        inv=pow(rows[pr][c],p-2,p); rows[pr]=[(x*inv)%p for x in rows[pr]]
        for r in range(m):
            if r!=pr and rows[r][c]%p:
                f=rows[r][c]; rows[r]=[(rows[r][j]-f*rows[pr][j])%p for j in range(nc)]
        pr+=1
        if pr==m: break
    return rows
def left_null(V,p):
    m=len(V); k=len(V[0]) if m else 0
    aug=[V[i][:]+[1 if j==i else 0 for j in range(m)] for i in range(m)]
    return [[row[k+j]%p for j in range(m)] for row in _rref(aug,p)
            if all(x%p==0 for x in row[:k]) and any(x%p for x in row[k:])]
def I0(S,p,k,a,b,w):
    n=len(S); pa_=[pow(int(x),a,p) for x in S]; pb_=[pow(int(x),b,p) for x in S]; g_set=set()
    for R in itertools.combinations(range(n),w):
        V=[[pow(int(S[i]),j,p) for j in range(k)] for i in R]; P=left_null(V,p)
        if not P: continue
        pa=[sum(P[t][ii]*pa_[R[ii]] for ii in range(w))%p for t in range(len(P))]
        pb=[sum(P[t][ii]*pb_[R[ii]] for ii in range(w))%p for t in range(len(P))]
        if not any(pb): continue
        i=next(j for j in range(len(pb)) if pb[j]); gg=(-pa[i]*pow(pb[i],p-2,p))%p
        if all((pa[t]+gg*pb[t])%p==0 for t in range(len(pb))) and gg!=0: g_set.add(gg)
    return len(g_set)

# (1) Linear-algebra realizability: for w <= k+1, EVERY R of size w yields exactly one alpha
#     (the (k+1)-subset solve is the FULL story; antipodal structure irrelevant).
print("(1) realizability: for w<=k+1 each size-w R forces 1 alpha (interpolation), Mann irrelevant.")
n,k=16,4; q=big_prime(n,n**4*4); S=gen_mu(q,n)
for w in [k+1]:
    cnt=I0(S,q,k,a=5,b=4,w=w)
    print(f"   n={n} k={k} a=5 b=4 w={w}=k+1: I0={cnt}  (C(n,w)={ __import__('math').comb(n,w)} size-w subsets)")

# (2) q-stability (char-0 faithfulness)
print("(2) q-stability of I0 (two big primes, same char-0 value expected):")
for (a,b,w) in [(10,4,6),(10,4,8),(9,8,9)]:
    q1=big_prime(16, 16**4*4); q2=big_prime(16, 16**4*40)
    S1=gen_mu(q1,16); S2=gen_mu(q2,16)
    v1=I0(S1,q1,4,a,b,w); v2=I0(S2,q2,4,a,b,w)
    print(f"   a={a} b={b} w={w}: I0(q={q1})={v1}  I0(q={q2})={v2}  {'STABLE' if v1==v2 else 'UNSTABLE'}")

# (3) EXACT-match rows = the w>=n-? saturated regime where R is forced antipodal/coset?
print("(3) EXACT-match (w=8 @n=16): the agreement set R there:")
def sets(S,p,k,a,b,w):
    n=len(S); pa_=[pow(int(x),a,p) for x in S]; pb_=[pow(int(x),b,p) for x in S]; out=[]
    for R in itertools.combinations(range(n),w):
        V=[[pow(int(S[i]),j,p) for j in range(k)] for i in R]; P=left_null(V,p)
        if not P: continue
        pa=[sum(P[t][ii]*pa_[R[ii]] for ii in range(w))%p for t in range(len(P))]
        pb=[sum(P[t][ii]*pb_[R[ii]] for ii in range(w))%p for t in range(len(P))]
        if not any(pb): continue
        i=next(j for j in range(len(pb)) if pb[j]); gg=(-pa[i]*pow(pb[i],p-2,p))%p
        if all((pa[t]+gg*pb[t])%p==0 for t in range(len(pb))) and gg!=0: out.append((R,gg))
    return out
ss=sets(S,q,4,10,4,8)
h=8
for R,g in ss[:8]:
    anti=all(((j+h)%16) in set(R) for j in R)
    print(f"   R={R} antipodal_closed={anti}")

#!/usr/bin/env python3
"""
FAST exact D for ONE direction via bitmask necklace enumeration (no per-subset O(ns) canon).
Enumerates s-subsets of Z/n as bitmasks; processes one representative per cyclic-rotation class
using a fast bit-rotation canonical test; weights each class's gamma by its orbit under <fac>.
Targets the crossing region (deeper s) for n up to ~28.
"""
import sys, math, itertools

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def fp(n, lo):
    p=lo+(1-lo)%n
    while True:
        if p>2 and p%n==1 and isprime(p): return p
        p+=n

def subgroup_ordered(p, n):
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): S.append(x); x=x*h%p
        if len(set(S))==n: return S,h
    raise RuntimeError("no subgroup")

def left_null(R, p, k, Spow):
    """left null space of the |R| x k Vandermonde [S_i^j]; R = list of indices."""
    s=len(R)
    A=[[Spow[j][R[i]]%p for j in range(k)]+[1 if jj==i else 0 for jj in range(s)] for i in range(s)]
    pr=0
    for c in range(k):
        sel=None
        for r in range(pr,s):
            if A[r][c]%p: sel=r; break
        if sel is None: continue
        A[pr],A[sel]=A[sel],A[pr]
        inv=pow(A[pr][c],p-2,p)
        A[pr]=[(x*inv)%p for x in A[pr]]
        for r in range(s):
            if r!=pr and A[r][c]%p:
                f=A[r][c]; A[r]=[(A[r][j]-f*A[pr][j])%p for j in range(k+s)]
        pr+=1
        if pr==s: break
    out=[]
    for r in range(s):
        if all(A[r][c]%p==0 for c in range(k)) and any(A[r][k+j]%p for j in range(s)):
            out.append([A[r][k+j]%p for j in range(s)])
    return out

def rotations_min(mask, n):
    """min over cyclic rotations of the bitmask (canonical form)."""
    full=(1<<n)-1
    best=mask
    cur=mask
    for _ in range(n-1):
        cur=((cur<<1)&full)|(cur>>(n-1))
        if cur<best: best=cur
    return best

def D_dir(S,h,p,k,a_exp,b,s,Spow):
    n=len(S)
    prec_a=Spow[a_exp]; prec_b=Spow[b]
    fac=pow(h,(b-a_exp)%n,p)
    gammas=set(); heavy=False
    seen=set()
    full=(1<<n)-1
    # enumerate subsets containing bit 0 (one per rotation class has its min-rotation start at 0-run)
    for rest in itertools.combinations(range(1,n), s-1):
        mask=1
        for r in rest: mask|=(1<<r)
        cm=rotations_min(mask,n)
        if cm!=mask:
            # only process if this IS the canonical (min) rotation
            if cm in seen: continue
            # skip non-canonical
            continue
        if mask in seen: continue
        seen.add(mask)
        R=[i for i in range(n) if (mask>>i)&1]
        P=left_null(R,p,k,Spow)
        if not P: continue
        pa=[sum(P[t][ii]*prec_a[R[ii]] for ii in range(s))%p for t in range(len(P))]
        pb=[sum(P[t][ii]*prec_b[R[ii]] for ii in range(s))%p for t in range(len(P))]
        if not any(pb):
            if not any(pa): heavy=True
            continue
        i=next(j for j in range(len(pb)) if pb[j])
        g=(-pa[i]*pow(pb[i],p-2,p))%p
        if all((pa[t]+g*pb[t])%p==0 for t in range(len(pb))):
            x=g
            for _ in range(n):
                gammas.add(x); x=(x*fac)%p
    if heavy: return p
    return len(gammas)

def run(n,k,s_lo,s_hi,blist,p=None):
    p=p or fp(n,200003)
    S,h=subgroup_ordered(p,n)
    Spow=[[pow(x,e,p) for x in S] for e in range(n)]
    print(f"[n={n} k={k} p={p}] blist={blist} bitmask necklace:", flush=True)
    res={}
    for s in range(s_lo,s_hi+1):
        best=(-1,None)
        for b in blist:
            if b>=s: continue
            for a_exp in range(n):
                if a_exp==b: continue
                D=D_dir(S,h,p,k,a_exp,b,s,Spow)
                if D>best[0]: best=(D,(a_exp,b))
        res[s]=best
        print(f"  s={s} r={n-s} m={s-k}: D={best[0]} binder={best[1]} {'GOOD' if best[0]<=n else 'bad'}", flush=True)
    return res

if __name__=='__main__':
    n=int(sys.argv[1]); k=int(sys.argv[2]); s_lo=int(sys.argv[3]); s_hi=int(sys.argv[4])
    blist=[int(x) for x in sys.argv[5].split(',')] if len(sys.argv)>5 else [k]
    run(n,k,s_lo,s_hi,blist)

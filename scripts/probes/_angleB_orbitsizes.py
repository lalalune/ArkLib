#!/usr/bin/env python3
"""
ANGLE B fine-grained: for ONE direction (a,b) at ONE size s, report the FULL orbit-size
histogram of the bad-gamma set under  gamma -> gamma * h^{b-a}.

Purpose: explain the 'BAD(D)' rows where D is NOT z + S*O for a single S.  The free-action
weld assumes EVERY nonzero orbit has size S = n/gcd(b-a,n).  When the histogram shows MULTIPLE
sizes, the bad set is a union of orbits of DIFFERENT sizes (short orbits at roots of unity), so
the clean single-S crossing law D = z + S*O does not literally apply; the true count is
D = z + sum_orbits |orbit|.  This tests whether the over-det worst direction is single-S.

Usage: _angleB_orbitsizes.py n k a b s [mult]
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
def subgroup_ordered(p,n):
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): S.append(x); x=x*h%p
        if len(set(S))==n: return S,h
    raise RuntimeError("no subgroup")
def _rref(rows,p):
    rows=[r[:] for r in rows]; m=len(rows); nc=len(rows[0]) if m else 0; pr=0
    for c in range(nc):
        sel=next((r for r in range(pr,m) if rows[r][c]%p),None)
        if sel is None: continue
        rows[pr],rows[sel]=rows[sel],rows[pr]
        inv=pow(rows[pr][c],p-2,p)
        rows[pr]=[(x*inv)%p for x in rows[pr]]
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
def gamma_for_R(R,S,p,k,a,b,prec,Vrows):
    s=len(R); V=[Vrows[i] for i in R]; P=left_null(V,p)
    if not P: return ('none',None)
    pa_=prec[a]; pb_=prec[b]
    pa=[sum(P[t][ii]*pa_[R[ii]] for ii in range(s))%p for t in range(len(P))]
    pb=[sum(P[t][ii]*pb_[R[ii]] for ii in range(s))%p for t in range(len(P))]
    if not any(pb):
        if not any(pa): return ('heavy',None)
        return ('none',None)
    i=next(j for j in range(len(pb)) if pb[j])
    g=(-pa[i]*pow(pb[i],p-2,p))%p
    if all((pa[t]+g*pb[t])%p==0 for t in range(len(pb))): return ('one',g)
    return ('none',None)

def main():
    n=int(sys.argv[1]); k=int(sys.argv[2]); a=int(sys.argv[3]); b=int(sys.argv[4]); s=int(sys.argv[5])
    mult=int(sys.argv[6]) if len(sys.argv)>6 else 4
    p=fp(n, n**mult)
    S,h=subgroup_ordered(p,n)
    prec={e:[pow(x,e,p) for x in S] for e in range(n)}
    Vrows={i:[pow(S[i],j,p) for j in range(k)] for i in range(n)}
    # collect ALL bad gammas (full enumeration, no shift-class dedup, to be safe)
    bad=set(); heavy=False
    for R in itertools.combinations(range(n),s):
        kind,g=gamma_for_R(R,S,p,k,a,b,prec,Vrows)
        if kind=='heavy': heavy=True
        elif kind=='one': bad.add(g)
    d=math.gcd((b-a)%n,n); orbsize_pred=n//d
    fac=pow(h,(b-a)%n,p)
    # orbit-size histogram under multiplication by fac
    bad_nz=bad-{0}
    visited=set(); sizes={}
    for g in bad_nz:
        if g in visited: continue
        orb=[]; x=g
        for _ in range(2*n+1):
            if x in bad_nz:
                if x not in visited: visited.add(x); orb.append(x)
            if x==g and orb: pass
            x=(x*fac)%p
            if x==g: break
        sz=len(orb)
        sizes[sz]=sizes.get(sz,0)+1
    print(f"# n={n} k={k} dir=({a},{b}) s={s} m={s-k} p={p}")
    print(f"#   gcd(b-a,n)=d={d}  predicted orbit size S=n/d={orbsize_pred}  ord(h^(b-a))={ (n//math.gcd((b-a)%n,n)) }")
    print(f"#   |bad|={len(bad)}  0-in-bad(z)={1 if 0 in bad else 0}  heavy={heavy}")
    print(f"#   orbit-size histogram (size: #orbits): {dict(sorted(sizes.items()))}")
    total=sum(sz*cnt for sz,cnt in sizes.items()) + (1 if 0 in bad else 0)
    print(f"#   reconstruct z + sum(size*count) = {total}  (== |bad| {len(bad)}? {total==len(bad)})")
    single = len(sizes)<=1
    print(f"#   SINGLE-S clean? {single}  (#distinct orbit sizes = {len(sizes)})")

if __name__=='__main__':
    main()

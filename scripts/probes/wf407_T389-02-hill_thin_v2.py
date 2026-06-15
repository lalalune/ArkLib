#!/usr/bin/env python3
"""
wf407 / T389-02-hill : THIN PRIZE REGIME census (v2, optimized).

Same exact bad-scalar census as thinregime.py but with ALL needed modular inverses precomputed
(domain-difference inverses dom[i]-dom[j], only n^2 of them), so it runs at p=65537 (n=16 thin).
"""
import itertools, sys, math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def primitive_root(p):
    fs=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fs.add(d);m//=d
        d+=1
    if m>1:fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def mu_n(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def census(dom, a, b, k, w, p, dinv):
    """bad-gamma count for dir(a,b). dinv[(i,j)] = inverse of (dom[i]-dom[j]) mod p (i!=j)."""
    n=len(dom)
    va=[pow(x,a,p) for x in dom]; vb=[pow(x,b,p) for x in dom]
    bad=set(); sat=False
    for S in itertools.combinations(range(n), w):
        # divided differences along S order; need dd of orders k..w-1 for both va,vb
        # Newton divided differences with cached inverse of (dom[S[i+order]]-dom[S[i]])
        ca=[va[i] for i in S]; cb=[vb[i] for i in S]
        gamma=None; ok=True; free_all=True
        for order in range(1,w):
            na=[]; nb=[]
            for i in range(w-order):
                inv=dinv[(S[i+order],S[i])]
                na.append(((ca[i+1]-ca[i])*inv)%p)
                nb.append(((cb[i+1]-cb[i])*inv)%p)
            ca=na; cb=nb
            if order>=k:
                Bj=ca[0]%p; Aj=cb[0]%p   # va residual coeff Bj (mult by gamma), vb residual Aj
                if Bj!=0 or Aj!=0: free_all=False
                if Bj==0:
                    if Aj!=0: ok=False; break
                else:
                    gj=(-Aj*pow(Bj,p-2,p))%p
                    if gamma is None: gamma=gj
                    elif gamma!=gj: ok=False; break
        if not ok: continue
        if gamma is None:
            if free_all: sat=True
        else:
            bad.add(gamma)
    return len(bad), sat

def run(n,k,p,w,amax=None,label=""):
    print(f"\n===== {label}: n={n} k={k} p={p} w={w} (rho={k/n:.3f}; n^4={n**4}, thin p>n^4:{p>n**4}; C(n,w)={math.comb(n,w)}) =====",flush=True)
    dom=mu_n(p,n)
    dinv={}
    for i in range(n):
        for j in range(n):
            if i!=j: dinv[(i,j)]=pow((dom[i]-dom[j])%p,p-2,p)
    amax=amax or n-1
    rows=[]
    for a in range(k,amax+1):
        for b in range(0,a):
            c,sat=census(dom,a,b,k,w,p,dinv)
            rows.append((a,b,c,sat))
    rows.sort(key=lambda r:-r[2])
    print(" top dir(a,b):",flush=True)
    for a,b,c,sat in rows[:10]:
        print(f"   dir(a={a:2d},b={b:2d}) I={c:5d} [{'ADJ' if a-b==1 else 'gap'+str(a-b)}]{' SAT' if sat else ''}",flush=True)
    bya={}
    for a,b,c,sat in rows: bya[a]=max(bya.get(a,-1),c)
    print(" max incidence per direction-exp a (LOW->HIGH):",flush=True)
    for a in sorted(bya): print(f"   a={a:2d}: maxI={bya[a]}",flush=True)
    bb=rows[0]
    print(f" => BEST dir(a={bb[0]},b={bb[1]}) I={bb[2]} [{'ADJ' if bb[0]-bb[1]==1 else 'gap'+str(bb[0]-bb[1])}]; "
          f"argmax-exp a*={max(bya,key=bya.get)} (k={k}, n/2={n//2})",flush=True)
    return bb

if __name__=="__main__":
    run(12,6,13,9,label="XCHK (12,6)")                          # gate: dir(9,8)=12
    run(16,8,65537,9,label="THIN (16,8) w=9")                   # n=16 thin regime, deep band
    run(16,8,65537,10,label="THIN (16,8) w=10")                 # one notch toward capacity
    run(16,8,65537,11,label="THIN (16,8) w=11")

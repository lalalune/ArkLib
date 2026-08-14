#!/usr/bin/env python3
"""
Test N-independence of the commit-phase soundness ratio by CONSTRUCTING the structurally-predicted
worst-case above-Johnson witness (no exhaustive search). Nesting analysis: the maximally-slack
above-Johnson witness packs its weight wmin into the FEWEST antipodal orbits (ceil(wmin/2) orbits,
2 per orbit) -> minimal folded support -> stays close through the most fold rounds. We build several
such witnesses at N=8,16,32, verify above-Johnson (genuine leader), compute the multi-round
commit-phase bad-count, and report the ratio c=bad/q^{nr-1}. If c is ~constant across N => candidate
N-independence; if it drifts => finite-size (as the nesting obstruction predicts).
"""
import itertools,random,math,functools
print=functools.partial(print,flush=True)
def run(q,N,k,ntry=40,seed=1):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    om=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if om is None or pow(om,N//2,q)!=q-1: print(f"skip q={q} N={N} (no 2^mu root)");return
    Ds=[[pow(om,i,q) for i in range(N)]]
    while len(Ds[-1])>1: Ds.append(sorted(set(pow(x,2,q) for x in Ds[-1])))
    nr=len(Ds)-1; inv2=inv[2]
    kdeg=[max(1,k>>L) for L in range(nr+1)]
    foldmap=[]
    for L in range(nr):
        prev,nxt=Ds[L],Ds[L+1];pos={v:i for i,v in enumerate(nxt)};seen=set();fm=[]
        for x in prev:
            y=pow(x,2,q)
            if y not in seen: seen.add(y);fm.append((pos[y],prev.index(x),prev.index((q-x)%q),x))
        foldmap.append((prev,nxt,fm))
    def fold1(vec,L,lam):
        prev,nxt,fm=foldmap[L];g=[0]*len(nxt)
        for (yi,xi,nxi,x) in fm:
            a=((vec[xi]+vec[nxi])*inv2)%q;b=((vec[xi]-vec[nxi])*inv[(2*x)%q])%q;g[yi]=(a+lam*b)%q
        return g
    def mindist(u,dom,kk):
        n=len(dom)
        if kk>=n: return 0
        best=kk-1
        for sub in itertools.combinations(range(n),kk):
            pts=[(dom[i],u[i]) for i in sub];ag=0
            for t in range(n):
                X=dom[t];tot=0
                for i,(xi,yi) in enumerate(pts):
                    term=yi
                    for j,(xj,_) in enumerate(pts):
                        if j!=i: term=(term*((X-xj)%q)*inv[(xi-xj)%q])%q
                    tot=(tot+term)%q
                if tot==u[t]: ag+=1
            if ag>best:best=ag
            if best==n: break
        return n-best
    rho=k/N;johnson=1-math.sqrt(rho);wmin=math.floor(johnson*N)+1
    radii=[(wmin*len(Ds[L]))//N for L in range(1,nr+1)]
    def commit_bad(f):
        cnt=0
        def rec(vec,L):
            nonlocal cnt
            if L==nr: cnt+=1;return
            for lam in range(q):
                nv=fold1(vec,L,lam)
                if mindist(nv,Ds[L+1],kdeg[L+1])<=radii[L]: rec(nv,L+1)
        rec(f,0);return cnt
    # construct: pack wmin into ceil(wmin/2) antipodal orbits (2 per orbit, 1 leftover)
    norb=N//2; random.seed(seed); best=-1; bestw=None; tried=0; goodleaders=0
    morb=math.ceil(wmin/2)
    for _ in range(ntry):
        orbs=random.sample(range(norb),morb)
        f=[0]*N; placed=0
        for o in orbs:
            # orbit = positions o and o+N/2
            f[o]=random.randrange(1,q); placed+=1
            if placed<wmin: f[o+N//2]=random.randrange(1,q); placed+=1
        if placed<wmin: continue
        tried+=1
        if mindist(f,Ds[0],k)!=wmin: continue   # genuine above-Johnson leader
        goodleaders+=1
        b=commit_bad(f)
        if b>best: best=b;bestw=orbs
    tot=q**nr; cval=best/(q**(nr-1)) if best>=0 else -1
    print(f" q={q} N={N} k={k} rho={rho:.2f} nr={nr} wmin={wmin} morb={morb} radii={radii}: "
          f"constructed worst commit-bad={best}/{tot}  c=bad/q^(nr-1)={cval:.3f}  ratio={best/tot if best>=0 else -1:.4f} (leaders {goodleaders}/{tried})")
print("Constructed minimal-folded-support worst-case witnesses, commit-phase ratio vs N (rho=1/2):")
run(97,8,4,ntry=30); run(97,16,8,ntry=30); run(97,32,16,ntry=12)

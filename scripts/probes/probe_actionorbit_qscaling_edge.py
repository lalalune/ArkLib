#!/usr/bin/env python3
"""
DECISIVE q-scaling test of the prize's above-Johnson O(1)/|F| claim, at the one clean non-vacuous
edge of the N=8 rho=1/2 model: GENUINE leader weight w=3 (true distance 3 > Johnson 2.34; matched
folded radius 1 position < folded covering radius 2, so non-vacuous).

CRITICAL fix vs first attempt: we restrict to GENUINE distance-3 leaders. A weight-3 vector f has
true distance d(f,RS_8)=3 iff its syndrome is NOT reachable by <=2 columns of H_N (else a codeword
is within 2 => below-Johnson coset). We precompute the set of <=2-column syndromes and filter.
Then maximize eps_matched = #{lambda: foldeddist(Fold[f,lambda],RS'[4,2]) <= 1} over genuine
distance-3 leaders. Constant worst-count as q grows => consistent with O(1)/|F|; growth => refutes.
"""
import itertools,math,random,functools
print=functools.partial(print,flush=True)
def run(q,N=8,k=4,samples=3000,seed=3):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    kp=k//2
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: return None
    D=[pow(omega,i,q) for i in range(N)];Dp=sorted(set(pow(x,2,q) for x in D));Np=len(Dp)
    # parity check H_N of RS_8 (deg<4): null space of 4x8 Vandermonde
    def pc(dom,kk):
        n=len(dom);G=[[pow(x,j,q) for x in dom]for j in range(kk)];M=[r[:]for r in G]
        rows=kk;cols=n;piv=[];r=0
        for c in range(cols):
            pr=next((i for i in range(r,rows) if M[i][c]%q),None)
            if pr is None: continue
            M[r],M[pr]=M[pr],M[r];ip=inv[M[r][c]%q];M[r]=[(v*ip)%q for v in M[r]]
            for i in range(rows):
                if i!=r and M[i][c]%q:
                    f=M[i][c]%q;M[i]=[(M[i][j]-f*M[r][j])%q for j in range(cols)]
            piv.append(c);r+=1
            if r==rows:break
        free=[c for c in range(cols)if c not in piv];H=[]
        for fc in free:
            h=[0]*cols;h[fc]=1
            for ri,p in enumerate(piv):h[p]=(-M[ri][fc])%q
            H.append(h)
        return H
    HN=pc(D,k);rN=len(HN)
    def syn(f): return tuple(sum(HN[i][j]*f[j] for j in range(N))%q for i in range(rN))
    # set of syndromes reachable by <=2 columns (true distance <=2 cosets)
    low=set();low.add(tuple([0]*rN))
    cols=[[HN[i][j] for i in range(rN)] for j in range(N)]
    for j in range(N):
        for a in range(1,q): low.add(tuple((a*cols[j][i])%q for i in range(rN)))
    for j1,j2 in itertools.combinations(range(N),2):
        for a in range(1,q):
            ac=[(a*cols[j1][i])%q for i in range(rN)]
            for b in range(1,q):
                low.add(tuple((ac[i]+b*cols[j2][i])%q for i in range(rN)))
    seen=set();fold=[]
    for x in D:
        y=pow(x,2,q);nx=(q-x)%q
        if y not in seen: seen.add(y);fold.append((Dp.index(y),x,nx))
    inv2=inv[2];pairs=list(itertools.combinations(range(Np),2))
    def fdist(u):
        best=1
        for(i,j)in pairs:
            xi,xj=Dp[i],Dp[j];slope=((u[j]-u[i])*inv[(xj-xi)%q])%q
            ag=sum(1 for t in range(Np) if (u[i]+slope*((Dp[t]-xi)%q))%q==u[t])
            if ag>best:best=ag
        return Np-best
    def epsM(f):
        fd={D[i]:f[i] for i in range(N)};g0=[0]*Np;g1=[0]*Np
        for(yi,x,nx)in fold:
            g0[yi]=((fd[x]+fd[nx])*inv2)%q;g1[yi]=((fd[x]-fd[nx])*inv[(2*x)%q])%q
        c=0
        for lam in range(q):
            u=[(g0[t]+lam*g1[t])%q for t in range(Np)]
            if fdist(u)<=1: c+=1
        return c
    random.seed(seed);best=-1;bs=None;checked=0;genuine=0
    for supp in itertools.combinations(range(N),3):
        itr=(itertools.product(range(1,q),repeat=3) if (q-1)**3<=50000
             else ([random.randrange(1,q) for _ in range(3)] for _ in range(samples)))
        for vals in itr:
            f=[0]*N
            for idx,v in zip(supp,vals): f[idx]=v
            checked+=1
            if syn(f) in low: continue      # not a genuine distance-3 leader (below-Johnson coset)
            genuine+=1
            e=epsM(f)
            if e>best: best=e;bs=(supp,tuple(vals))
    return best,bs,genuine,checked
print("q-scaling, GENUINE distance-3 leaders only (above-Johnson edge, RS[8,4], folded radius 1/4):")
for q in [17,41,73,97,193,257]:
    r=run(q)
    if r: print(f"   q={q:4d}: worst eps_matched = {r[0]:3d}/{q}  ratio={r[0]/q:.4f}  (genuine leaders sampled={r[2]}/{r[3]})  witness supp={r[1][0] if r[1] else None}")

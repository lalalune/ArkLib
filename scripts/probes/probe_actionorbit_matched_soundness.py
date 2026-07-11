#!/usr/bin/env python3
"""
FAITHFUL exhaustive FRI soundness test (matched relative radius, EXACT folded distance) -- the
honest version after finding eps0 trivial (line-meets-subspace<=1) and eps1 vacuous (folded
covering radius). For RS[N,k] with kp=k/2 and Np=N/2:

A coset with leader weight w (relative distance zeta=w/N) is a genuine above-Johnson soundness
violation for challenge lambda iff the folded word Fold[f,lambda] is within the SAME relative
radius zeta of RS', i.e. within  ceil-ish  zeta*Np = w*Np/N = w/2  positions of RS'[Np,kp].

We compute EXACT folded Hamming distance to RS'[Np,kp] (kp=2: via the C(Np,2) line-fits; a nearest
deg<2 codeword agreeing on >=2 pts is determined by 2 of them, so min-dist = Np - max over point
pairs of agreements). eps_matched(f) = #{lambda : foldeddist(lambda) <= floor(w/2)}.

Exhaustive over the ENTIRE adversary coset space (syndrome-invariant). Reports max eps_matched
bucketed by leader weight w, flagging above-Johnson w. Conj 7.1: worst above-J eps at minimal w.
"""
import itertools, math, functools
print=functools.partial(print,flush=True)
def gf(q):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    return inv
def pc(dom,kk,q,inv):
    n=len(dom);G=[[pow(x,j,q) for x in dom] for j in range(kk)]
    M=[r[:] for r in G];rows=kk;cols=n;piv=[];r=0
    for c in range(cols):
        pr=next((i for i in range(r,rows) if M[i][c]%q),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r];ip=inv[M[r][c]%q];M[r]=[(v*ip)%q for v in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]%q:
                f=M[i][c]%q;M[i]=[(M[i][j]-f*M[r][j])%q for j in range(cols)]
        piv.append(c);r+=1
        if r==rows: break
    free=[c for c in range(cols) if c not in piv];H=[]
    for fc in free:
        h=[0]*cols;h[fc]=1
        for ri,pcx in enumerate(piv): h[pcx]=(-M[ri][fc])%q
        H.append(h)
    return H
def run(q,N,k):
    inv=gf(q);kp=k//2
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: print(f"skip q={q} N={N}");return
    D=[pow(omega,i,q) for i in range(N)];Dp=sorted(set(pow(x,2,q) for x in D));Np=len(Dp)
    if kp!=2: print(f"skip kp={kp} (exact-dist impl is kp=2 only)"); return
    HN=pc(D,k,q,inv);rN=len(HN)
    posDp={v:i for i,v in enumerate(Dp)};seen=set();fold=[]
    for x in D:
        y=pow(x,2,q);nx=(q-x)%q
        if y not in seen: seen.add(y);fold.append((posDp[y],x,nx))
    inv2=inv[2]
    # precompute the C(Np,2) point-pair lines (deg<2) for exact distance to RS'[Np,kp=2]
    pairs=list(itertools.combinations(range(Np),2))
    # for a folded word u (list len Np), min dist = Np - max agreements with a deg<2 poly.
    # a deg<2 poly is determined by values at 2 points; for pair (i,j) the line through (Dp[i],u[i]),(Dp[j],u[j]).
    def folded_dist(u):
        best_ag=1  # at least 1 (any single point) but lines need 2; codeword agreeing on>=2 is a pair-line
        for (i,j) in pairs:
            xi,xj=Dp[i],Dp[j]; yi,yj=u[i],u[j]
            # line value at x: yi + (yj-yi)*(x-xi)/(xj-xi)
            slope=((yj-yi)*inv[(xj-xi)%q])%q
            ag=sum(1 for t in range(Np) if (yi+slope*((Dp[t]-xi)%q))%q==u[t])
            if ag>best_ag: best_ag=ag
        return Np-best_ag
    def synN(f): return tuple(sum(HN[i][j]*f[j] for j in range(N))%q for i in range(rN))
    def epsM(f,w):
        fd={D[i]:f[i] for i in range(N)};g0=[0]*Np;g1=[0]*Np
        for (yi,x,nx) in fold:
            g0[yi]=((fd[x]+fd[nx])*inv2)%q;g1[yi]=((fd[x]-fd[nx])*inv[(2*x)%q])%q
        radius=w//2   # matched: zeta*Np = w/2 positions
        c=0
        for lam in range(q):
            u=[(g0[t]+lam*g1[t])%q for t in range(Np)]
            if folded_dist(u)<=radius: c+=1
        return c
    cov=N-k;leader={}
    for w in range(0,cov+1):
        for supp in itertools.combinations(range(N),w):
            for vals in itertools.product(range(1,q),repeat=w):
                f=[0]*N
                for idx,v in zip(supp,vals): f[idx]=v
                s=synN(f)
                if s not in leader or leader[s][0]>w: leader[s]=(w,f)
        if len(leader)==q**rN: break
    rho=k/N;johnson=1-math.sqrt(rho);jpos=johnson*N
    print(f"\n===== q={q} N={N} k={k} rho={rho:.3f} | Np={Np} kp={kp} | Johnson={johnson:.3f}({jpos:.2f}pos) | cosets={q**rN} =====")
    byw={};supw={}
    for s,(w,f) in leader.items():
        e=epsM(f,w)
        if e>byw.get(w,-1): byw[w]=e;supw[w]=tuple(i for i in range(N) if f[i])
    for w in sorted(byw):
        tag=" <ABOVE-J>" if w>jpos else ""
        print(f"   w={w} (relradius {w}/{N}={w/N:.3f}, matched folded radius {w//2}/{Np}): max eps_matched={byw[w]:3d}/{q}{tag}  worstsupp={supw[w]}")
    aj=[w for w in sorted(byw) if w>jpos]
    if aj:
        m=max(byw[w] for w in aj);first=min(w for w in aj if byw[w]==m)
        print(f"   ABOVE-JOHNSON worst eps_matched = {m}/{q} (= {m/q:.4f}); first at w={first}, minimal above-J w={min(aj)}")
        print(f"   => above-Johnson soundness is {'O(1)/|F| small' if m<=2 else f'LARGE ({m}/{q})'}; "
              f"3-pos dominance: {'YES' if first==min(aj) else f'NO (w={first})'}")
for (q,N,k) in [(17,8,4),(41,8,4),(97,8,4),(17,16,8)]:
    run(q,N,k)

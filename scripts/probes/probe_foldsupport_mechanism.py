#!/usr/bin/env python3
"""
NOVEL structural finding + mechanism for the above-Johnson FRI O(1) bound.
DISCOVERY (from this campaign's own worst-case witnesses): the worst above-Johnson witness, after one
fold (antipodal collapse i ~ i+N/2), is supported on a SMALL number m of FOLDED positions:
  N=8 worst (0,1,2) -> mod 4 = {0,1,2} (m=3);  N=16 worst (1,5,7,9,15) -> mod 8 = {1,5,7} (m=3).
=> "3-position sparse witness" = error collapses to 3 positions in the folded domain D^2.

MECHANISM (provable): if f's deviation from a codeword folds to m positions, the folded word
f_lambda = (lifted codeword) + delta, delta supported on those m folded positions with values
e_e[t]+lambda*e_o[t]. Each position vanishes at exactly one lambda, so the ALIGNED-codeword bad
count <= m (indep of N,q). This probe: (1) confirms worst-case witnesses fold to small m; (2)
measures worst-case bad-count as a function of m (folded-support size) and N.
"""
import itertools,random,math,functools
print=functools.partial(print,flush=True)
def setup(q,N,k):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    kp=k//2
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: return None
    D=[pow(omega,i,q) for i in range(N)];Dp=sorted(set(pow(x,2,q) for x in D));Np=len(Dp)
    seen=set();fold=[]
    for x in D:
        y=pow(x,2,q);nx=(q-x)%q
        if y not in seen: seen.add(y);fold.append((Dp.index(y),x,nx))
    inv2=inv[2];Dq=list(itertools.combinations(range(Np),kp))
    # parity check H_N of RS_N for genuine-leader test (syndrome not reachable by <=2 cols => dist>=3)
    def pcmat(dom,kk):
        n=len(dom);G=[[pow(x,j,q)for x in dom]for j in range(kk)];M=[r[:]for r in G];rows=kk;cols=n;piv=[];r=0
        for c in range(cols):
            pr=next((i for i in range(r,rows) if M[i][c]%q),None)
            if pr is None:continue
            M[r],M[pr]=M[pr],M[r];ip=inv[M[r][c]%q];M[r]=[(v*ip)%q for v in M[r]]
            for i in range(rows):
                if i!=r and M[i][c]%q:
                    fv=M[i][c]%q;M[i]=[(M[i][j]-fv*M[r][j])%q for j in range(cols)]
            piv.append(c);r+=1
            if r==rows:break
        free=[c for c in range(cols)if c not in piv];H=[]
        for fc in free:
            h=[0]*cols;h[fc]=1
            for ri,pp in enumerate(piv):h[pp]=(-M[ri][fc])%q
            H.append(h)
        return H
    HN=pcmat(D,k);rN=len(HN);Hc=[[HN[i][j] for i in range(rN)] for j in range(N)]
    low=set();low.add(tuple([0]*rN))
    for j in range(N):
        for a in range(1,q): low.add(tuple((a*Hc[j][i])%q for i in range(rN)))
    for j1,j2 in itertools.combinations(range(N),2):
        for a in range(1,q):
            ac=[(a*Hc[j1][i])%q for i in range(rN)]
            for b in range(1,q): low.add(tuple((ac[i]+b*Hc[j2][i])%q for i in range(rN)))
    def synN(f): return tuple(sum(HN[i][j]*f[j] for j in range(N))%q for i in range(rN))
    def is_leader(f): return synN(f) not in low
    def fdist(u):
        best=kp-1
        for sub in Dq:
            pts=[(Dp[i],u[i]) for i in sub]
            ag=0
            for t in range(Np):
                X=Dp[t];tot=0
                for i,(xi,yi) in enumerate(pts):
                    term=yi
                    for j,(xj,_) in enumerate(pts):
                        if j!=i: term=(term*((X-xj)%q)*inv[(xi-xj)%q])%q
                    tot=(tot+term)%q
                if tot==u[t]: ag+=1
            if ag>best: best=ag
            if best==Np: break
        return Np-best
    def foldsupp(e):  # antipodal orbits hit
        return len(set(i%(N//2) for i in range(N) if e[i]))
    def badcount(f,radius):
        fd={D[i]:f[i] for i in range(N)};g0=[0]*Np;g1=[0]*Np
        for(yi,x,nx)in fold:
            g0[yi]=((fd[x]+fd[nx])*inv2)%q;g1[yi]=((fd[x]-fd[nx])*inv[(2*x)%q])%q
        c=0
        for lam in range(q):
            u=[(g0[t]+lam*g1[t])%q for t in range(Np)]
            if fdist(u)<=radius: c+=1
        return c
    return dict(q=q,N=N,k=k,kp=kp,D=D,Np=Np,foldsupp=foldsupp,badcount=badcount,inv=inv,is_leader=is_leader)
def run(q,N,k,trials=8000,seed=9):
    S=setup(q,N,k)
    if S is None: print(f"skip {q},{N}");return
    N,Np=S['N'],S['Np'];rho=k/N;johnson=1-math.sqrt(rho)
    wmin=math.floor(johnson*N)+1;radius=(wmin*Np)//N
    random.seed(seed)
    # bucket worst bad-count by folded-support size m, over above-Johnson weight-wmin words
    bym={}; wit={}
    supps=list(itertools.combinations(range(N),wmin))
    for _ in range(trials):
        supp=random.choice(supps);f=[0]*N
        for idx in supp: f[idx]=random.randrange(1,q)
        if not S['is_leader'](f): continue
        m=S['foldsupp'](f)
        b=S['badcount'](f,radius)
        if b>bym.get(m,-1): bym[m]=b;wit[m]=supp
    print(f"\n q={q} N={N} k={k} rho={rho:.2f} Johnson={johnson*N:.2f}pos wmin={wmin} radius={radius}/{Np}:")
    for m in sorted(bym):
        print(f"   folded-support m={m}: worst bad-count={bym[m]:3d}/{q}   (e.g. supp {wit[m]} -> folds to {sorted(set(i%(N//2) for i in wit[m]))})")
    gm=max(bym,key=lambda m:bym[m])
    print(f"   => overall worst bad-count={bym[gm]} at folded-support m={gm}")
print("Mechanism test: worst-case bad-count vs folded-support size m (rho=1/2, above-Johnson weight):")
run(17,8,4); run(41,8,4); run(17,16,8)

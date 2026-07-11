#!/usr/bin/env python3
"""
MULTI-ROUND FRI commit-phase soundness (canonical BCIKS def) -- the RIGHT object for the prize O(1)/|F|
claim (2026/861), which the single-fold proxy could not reach. f_0 far from RS[N,k]; fold through all
rounds N -> N/2 -> ... -> 2 with challenges (lambda_1,...). A challenge tuple is BAD (adversary 'accepted')
if proximity is maintained at EVERY round: f_j within matched radius of RS_j for all j. We compute the
worst-case bad-count over genuine above-Johnson leaders f_0, and its scaling with N. O(1) (const in N) =>
supports the prize claim; O(n) growth => the action-orbit improvement is needed / claim is finer.
"""
import itertools,random,math,functools
print=functools.partial(print,flush=True)
def build(q,N):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: return None
    return inv,omega
def domains(q,N,omega):
    Ds=[];D=[pow(omega,i,q) for i in range(N)];Ds.append(D)
    while len(Ds[-1])>1:
        prev=Ds[-1];nxt=sorted(set(pow(x,2,q) for x in prev));Ds.append(nxt)
    return Ds
def run(q,N,k,trials=3000,seed=4):
    bb=build(q,N)
    if bb is None: print(f"skip {q},{N}");return
    inv,omega=bb;Ds=domains(q,N,omega);nr=len(Ds)-1   # number of fold rounds (until size 1)
    inv2=inv[2]
    # per level L: domain Ds[L], code degree kL = k/2^L
    kdeg=[max(1,k>>L) for L in range(nr+1)]
    # fold maps per level: from Ds[L] to Ds[L+1]
    foldmap=[]
    for L in range(nr):
        prev=Ds[L];nxt=Ds[L+1];pos={v:i for i,v in enumerate(nxt)};seen=set();fm=[]
        for x in prev:
            y=pow(x,2,q);nx=(q-x)%q
            if y not in seen: seen.add(y);fm.append((pos[y],prev.index(x),prev.index(nx),x))
        foldmap.append((prev,nxt,fm))
    def fold_once(vec,L,lam):
        prev,nxt,fm=foldmap[L];g=[0]*len(nxt)
        for (yi,xi,nxi,x) in fm:
            g0=((vec[xi]+vec[nxi])*inv2)%q;g1=((vec[xi]-vec[nxi])*inv[(2*x)%q])%q
            g[yi]=(g0+lam*g1)%q
        return g
    def mindist(u,dom,kk):  # exact min Hamming dist to RS deg<kk on dom (kk small)
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
            if ag>best: best=ag
            if best==n: break
        return n-best
    # parity check + leader filter (genuine distance-w) for RS[N,k]
    def pc(dom,kk):
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
    HN=pc(Ds[0],k);rN=len(HN);Hc=[[HN[i][j]for i in range(rN)]for j in range(N)]
    rho=k/N;johnson=1-math.sqrt(rho);wmin=math.floor(johnson*N)+1
    # genuine distance-wmin leader. Exact (small N) or probabilistic k-subset sampling (large N).
    import random as _r
    def is_leader(f):
        if N<=8: return mindist(f,Ds[0],k)==wmin
        w=sum(1 for v in f if v); target=N-w+1
        for _ in range(40):
            sub=_r.sample(range(N),k); pts=[(Ds[0][i],f[i]) for i in sub]; ag=0
            for t in range(N):
                X=Ds[0][t];tot=0
                for i,(xi,yi) in enumerate(pts):
                    term=yi
                    for j,(xj,_) in enumerate(pts):
                        if j!=i: term=(term*((X-xj)%q)*inv[(xi-xj)%q])%q
                    tot=(tot+term)%q
                if tot==f[t]: ag+=1
            if ag>=target: return False
        return True
    # matched radius per level for a word at relative distance delta0=wmin/N: radius_L = floor(delta0*|D_L|)
    radii=[ (wmin*len(Ds[L]))//N for L in range(1,nr+1)]
    def commit_badcount(f):
        # count challenge tuples (lambda_1..lambda_nr) with proximity maintained at every round
        cnt=0
        def rec(vec,L):
            nonlocal cnt
            if L==nr: cnt+=1; return
            for lam in range(q):
                nv=fold_once(vec,L,lam)
                if mindist(nv,Ds[L+1],kdeg[L+1])<=radii[L]:
                    rec(nv,L+1)
        rec(f,0); return cnt
    random.seed(seed);best=-1;bs=None;ng=0
    supps=list(itertools.combinations(range(N),wmin))
    T=trials if N<=8 else trials//3
    for _ in range(T):
        supp=random.choice(supps);f=[0]*N
        for idx in supp: f[idx]=random.randrange(1,q)
        if not is_leader(f): continue
        ng+=1
        b=commit_badcount(f)
        if b>best: best=b;bs=supp
    tot=q**nr
    print(f" q={q} N={N} k={k} rho={rho:.2f} rounds={nr} Johnson={johnson*N:.2f}pos wmin={wmin} radii={radii}: "
          f"worst commit-bad-count={best}/{tot}  (ratio={best/tot:.4f}, leaders={ng}/{T}) worstsupp={bs}")
    return best
print("Multi-round FRI COMMIT-PHASE worst-case bad-count over above-Johnson leaders (rho=1/2):")
# stress-test: vary rate, field, N; also report against the trivial linear baseline
# N-independence test of c(rho): N=16 rho=1/2 (predict c=1) and rho=1/4 (predict c=6)
for cfg in [(17,16,8),(41,16,8),(17,16,4)]:
    run(*cfg)

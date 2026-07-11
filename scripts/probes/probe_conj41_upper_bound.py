import itertools, random, functools
print=functools.partial(print,flush=True)
exec(open('scripts/probes/probe_conj41_kernel.py').read().split('print("=== Conj41')[0])
def kbasis(M,p):
    R=len(M);C=len(M[0]);A=[r[:] for r in M];wh=[-1]*C;pr=0
    for c in range(C):
        pv=next((i for i in range(pr,R) if A[i][c]%p!=0),None)
        if pv is None: continue
        A[pr],A[pv]=A[pv],A[pr];iv=pow(A[pr][c]%p,p-2,p);A[pr]=[(x*iv)%p for x in A[pr]]
        for i in range(R):
            if i!=pr and A[i][c]%p!=0:
                f=A[i][c]%p;A[i]=[(A[i][j]-f*A[pr][j])%p for j in range(C)]
        wh[c]=pr;pr+=1
    pivs=[c for c in range(C) if wh[c]!=-1];fr=[c for c in range(C) if wh[c]==-1];B=[]
    for fc in fr:
        v=[0]*C;v[fc]=1
        for c in pivs: v[c]=(-A[wh[c]][fc])%p
        B.append(v)
    return B
def gam(E,L,D,c,p,s1,s2):
    N=normals(E,L,D,c,p);a=[sum(N[i][j]*s1[j] for j in range(D))%p for i in range(c)]
    b=[sum(N[i][j]*s2[j] for j in range(D))%p for i in range(c)];g=None
    for i in range(c):
        if b[i]%p==0:
            if a[i]%p!=0: return None
        else:
            gi=(-a[i]*pow(b[i],p-2,p))%p
            if g is None: g=gi
            elif g!=gi: return None
    return g
def Mtrue(s1,s2,n,w,D,c,p,L,subs):
    good=set()
    for E in subs:
        ge=gam(E,L,D,c,p,s1,s2)
        if ge is None: continue
        s=[(s1[j]+ge*s2[j])%p for j in range(D)];v=solve_unique(vander(E,L,D,p),s,p)
        if v is not None and all(x%p!=0 for x in v): good.add(ge)
    return len(good)

print("=== UPPER BOUND search: is max M_true > w+1 anywhere? (n=20,c=5,w=5; n=24,c=5,w=7) ===")
for (n,k,c) in [(20,10,5),(24,12,5)]:
    D=n-k;w=D-c;p=1000003; rng=random.Random(2); L=rng.sample(range(1,p),n)
    subs=list(itertools.combinations(range(n),w)); target=w+2; best=0; bestcfg=None
    # try MANY random (w+2)-support sets; build common-line kernel; count genuine M_true
    for _ in range(4000):
        Es=rng.sample(subs, target)
        gs=[rng.randrange(1,p) for _ in range(target)]
        if len(set(gs))<target: continue
        A=build_A(Es,gs,L,D,c,p)
        kb=kbasis(A,p)
        for kv in kb[:2]:
            s1=kv[:D];s2=kv[D:]
            if all(x%p==0 for x in s1) and all(x%p==0 for x in s2): continue
            m=Mtrue(s1,s2,n,w,D,c,p,L,subs)
            if m>best: best=m; bestcfg=Es
    # also: union of two (w+1)-cliques sharing w points (i.e. a (w+2)-set is the same as fat-clique; try sharing fewer)
    print(f"  n={n} c={c} w={w}: best M_true over 4000 random (w+2)-support configs = {best}  "
          f"(w+1={w+1}; {'NO config exceeds w+1 => max=w+1=D-c+1 supported' if best<=w+1 else f'EXCEEDS: {best}'})")

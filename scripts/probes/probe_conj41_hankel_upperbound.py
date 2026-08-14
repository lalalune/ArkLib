import itertools, functools, random
print=functools.partial(print,flush=True)
exec(open('scripts/probes/probe_conj41_kernel.py').read().split('print("=== Conj41')[0])
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
    return good
def hankel(s,w,c):  # c x (w+1) Hankel [s_{i+j}]
    return [[s[i+j] for j in range(w+1)] for i in range(c)]
def detmod_sq(M,p):
    M=[r[:] for r in M];n=len(M);det=1
    for c in range(n):
        piv=next((i for i in range(c,n) if M[i][c]%p!=0),None)
        if piv is None: return 0
        if piv!=c: M[c],M[piv]=M[piv],M[c];det=(-det)%p
        det=(det*M[c][c])%p;inv=pow(M[c][c]%p,p-2,p)
        for i in range(c+1,n):
            if M[i][c]%p:
                f=(M[i][c]*inv)%p;M[i]=[(M[i][j]-f*M[c][j])%p for j in range(n)]
    return det%p
# c=w+1 (square Hankel), unique-decoding regime: D=2w+1
w=3; c=4; D=w+c; n=8; k=n-D; p=1009; L=list(range(n)); subs=list(itertools.combinations(range(n),w))
rng=random.Random(0)
print(f"Unique-dec regime c=w+1: n={n} k={k} D={D} w={w} c={c} (c>=w+1: {c>=w+1}); bound w+1={w+1}")
# verify: M_true <= w+1 over many lines, AND det(H_w(s(gamma))) is a poly of degree<=w+1 in gamma whose roots contain decodable gammas
maxM=0
for _ in range(2000):
    s1=[rng.randrange(p) for _ in range(D)]; s2=[rng.randrange(p) for _ in range(D)]
    M=Mtrue(s1,s2,n,w,D,c,p,L,subs); maxM=max(maxM,len(M))
    # check each decodable gamma is a root of det(H_w(s(gamma)))
    for g in M:
        s=[(s1[j]+g*s2[j])%p for j in range(D)]
        if detmod_sq(hankel(s,w,c),p)!=0:
            print("  !! decodable gamma not a Hankel-det root (bug)"); break
# degree of det(H_w(s1+gamma s2)) in gamma: interpolate, find degree
xs=list(range(w+2)); ys=[]
s1=[rng.randrange(p) for _ in range(D)]; s2=[rng.randrange(p) for _ in range(D)]
for gv in xs:
    s=[(s1[j]+gv*s2[j])%p for j in range(D)]; ys.append(detmod_sq(hankel(s,w,c),p))
# Lagrange -> coeffs, find top nonzero
M2=[[pow(xs[i],j,p) for j in range(w+2)] for i in range(w+2)]
# solve
Aug=[M2[i][:]+[ys[i]] for i in range(w+2)];nn=w+2;where=[-1]*nn;pr=0
for col in range(nn):
    piv=next((i for i in range(pr,nn) if Aug[i][col]%p!=0),None)
    if piv is None: continue
    Aug[pr],Aug[piv]=Aug[piv],Aug[pr];inv=pow(Aug[pr][col]%p,p-2,p);Aug[pr]=[(x*inv)%p for x in Aug[pr]]
    for i in range(nn):
        if i!=pr and Aug[i][col]%p:
            f=Aug[i][col]%p;Aug[i]=[(Aug[i][j]-f*Aug[pr][j])%p for j in range(nn+1)]
    where[col]=pr;pr+=1
coef=[0]*nn
for col in range(nn):
    if where[col]!=-1: coef[col]=Aug[where[col]][nn]%p
deg=max([j for j in range(nn) if coef[j]!=0], default=-1)
print(f"  max M_true over 2000 lines = {maxM} (<= w+1={w+1}: {maxM<=w+1})")
print(f"  deg_gamma det(H_w(s1+gamma s2)) = {deg} (<= w+1={w+1}: {deg<=w+1}) => # decodable gamma <= #roots <= deg <= w+1  QED(c>=w+1)")

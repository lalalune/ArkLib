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
def Mtrue_count(s1,s2,n,w,D,c,p,L,subs,cap=None):
    good=set()
    for E in subs:
        ge=gam(E,L,D,c,p,s1,s2)
        if ge is None: continue
        s=[(s1[j]+ge*s2[j])%p for j in range(D)];v=solve_unique(vander(E,L,D,p),s,p)
        if v is not None and all(x%p!=0 for x in v): good.add(ge)
    return good
# Build a DEGENERATE line inside a single Im(V_E): s1=V_E e1, s2=V_E e2 for one support E, small p so we can scan all gamma
n,k,c=12,6,3; D=n-k; w=D-c; p=101; L=list(range(n)); subs=list(itertools.combinations(range(n),w))
rng=random.Random(1); E=tuple(range(w))   # support {0,1,2,3,4,5}
e1=[rng.randrange(1,p) for _ in range(w)]; e2=[rng.randrange(1,p) for _ in range(w)]
s1=mvp=[sum(vander(E,L,D,p)[i][j]*e1[j] for j in range(w))%p for i in range(D)]
s2=[sum(vander(E,L,D,p)[i][j]*e2[j] for j in range(w))%p for i in range(D)]
# count genuine decodable gamma by SCANNING all gamma in F_p (exact), via the single support E (and all subs)
cntE=0
for g in range(p):
    s=[(s1[j]+g*s2[j])%p for j in range(D)]; v=solve_unique(vander(E,L,D,p),s,p)
    if v is not None and all(x%p!=0 for x in v): cntE+=1
M=Mtrue_count(s1,s2,n,w,D,c,p,L,subs)
print(f"DEGENERATE line (s1,s2 in Im(V_E), E={E}), n={n} c={c} w={w} p={p}:")
print(f"  # gamma decodable by THAT single E (scan all p) = {cntE}  (expected ~ p-w = {p-w})")
print(f"  full M_true(s1,s2) over all supports = {len(M)}  (vs w+1={w+1}, bound floor((2D-1)/c)={(2*D-1)//c})")
print(f"  => degenerate lines (line inside one Im(V_E)) give M_true ~ p, MUCH larger than w+1.")
print(f"  => Conj41 / the w+1 law must be about NON-DEGENERATE lines (FRI-fold lines), excluding these.")

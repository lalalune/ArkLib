#!/usr/bin/env python3
"""Independent characteristic-43 six-pencil audit. Standard library only."""
import json,itertools,math
P=43
assert all(P%d for d in range(2,math.isqrt(P)+1))
B=[[10,18,19],[36,37,40],[17,0,9]]
C=[[6,32,1],[30,3,17],[9,12,20]]
POINTS=[[1,20,7],[1,39,12],[1,17,13],[1,31,20],[1,29,26],[1,42,30]]
EXPECTED_ROOTS=[[1,20,22,36],[0,15,20,39],[20,29,34,42],[22,32,39,42],[1,15,29,32],[0,32,34,36]]
EXPECTED_GAMMAS=[[30,29,38,19],[29,5,1,34],[32,40,6,7],[14,21,26,41],[2,17,9,28],[12,23,35,42]]

def clean(a):
    a=[x%P for x in a]
    while len(a)>1 and not a[-1]:a.pop()
    return a

def add(a,b):return clean([(a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))])
def scale(a,c):return clean([c*x for x in a])
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return clean(c)
def ev(a,x):
    y=0
    for c in a[::-1]:y=(y*x+c)%P
    return y

def divide(a,b):
    a=clean(a);q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);c=a[-1]*pow(b[-1],-1,P)%P;q[j]=c
        a=sub(a,[0]*j+scale(b,c))
    return clean(q),a

def exact(a,b):
    q,r=divide(a,b);assert r==[0];return q

def gcd(a,b):
    while b!=[0]:a,b=b,divide(a,b)[1]
    return scale(a,pow(a[-1],-1,P))

def dot(a,b):
    r=[0]
    for x,y in zip(a,b):r=add(r,mul(x,y))
    return r

def cross(a,b):return [sub(mul(a[(j+1)%3],b[(j+2)%3]),mul(a[(j+2)%3],b[(j+1)%3])) for j in range(3)]
def locator(xs):
    r=[1]
    for x in xs:r=mul(r,[-x,1])
    return r

def rr(a):
    a=[[v%P for v in row] for row in a];r=0;ps=[]
    for c in range(len(a[0])):
        pi=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pi is None:continue
        a[r],a[pi]=a[pi],a[r];iv=pow(a[r][c],-1,P);a[r]=[v*iv%P for v in a[r]]
        for i in range(len(a)):
            if i!=r:
                f=a[i][c];a[i]=[(x-f*y)%P for x,y in zip(a[i],a[r])]
        ps.append(c);r+=1
        if r==len(a):break
    return a,ps

def rank(a):return len(rr(a)[1])
def coeff_map(w,t):
    columns=[[0]*j+a for a in w for j in range(t+1)]
    return [[a[i] if i<len(a) else 0 for a in columns] for i in range(t+max(map(len,w)))]

w=cross(B,C)
assert max(map(len,w))==5 and rank([f+[0]*(5-len(f)) for f in w])==3
T=coeff_map(w,1);assert len(T)==6 and rank(T)==6
rawW=[dot([[c] for c in ci],w) for ci in POINTS]
assert all(len(f)==5 for f in rawW)
W=[scale(f,pow(f[-1],-1,P)) for f in rawW]
ci=[[(a*pow(f[-1],-1,P))%P for a in row] for f,row in zip(rawW,POINTS)]
roots=[[x for x in range(P) if ev(f,x)==0] for f in W]
assert roots==EXPECTED_ROOTS
assert len({tuple(f) for f in W})==6
common=W[0]
for f in W[1:]:common=gcd(common,f)
assert common==[1]
base=sorted(set.union(*(set(a) for a in roots)))
assert base==[0,1,15,20,22,29,32,34,36,39,42]
assert all(len(set(a)&set(b))==1 for a,b in itertools.combinations(roots,2))
assert rank(ci)==3
# Directions from the base frame alone, independently of the received-word reconstruction.
frame_gammas=[]
for row,rs in zip(ci,roots):
    gammas=[]
    for x in rs:
        bx=[ev(f,x) for f in B];cx=[ev(f,x) for f in C]
        j,k=next((j,k) for j,k in itertools.combinations(range(3),2) if (bx[j]*cx[k]-bx[k]*cx[j])%P)
        det=(bx[j]*cx[k]-bx[k]*cx[j])%P
        lam=(row[j]*cx[k]-row[k]*cx[j])*pow(det,-1,P)%P
        mu=(bx[j]*row[k]-bx[k]*row[j])*pow(det,-1,P)%P
        assert mu and all((lam*a+mu*b)%P==v for a,b,v in zip(bx,cx,row))
        gammas.append(-lam*pow(mu,-1,P)%P)
    assert len(set(gammas))==4;frame_gammas.append(gammas)
assert frame_gammas==EXPECTED_GAMMAS
all_gammas=sum(frame_gammas,[])
assert len(set(all_gammas))==23 and {g for g in all_gammas if all_gammas.count(g)>1}=={29}
# V_base has degree eleven. The required Bezout bound is seven, not six.
V=locator(base);L=coeff_map(w,7)
assert len(L)==12 and rank(L)==12
reduced,pivots=rr([row+[V[i]] for i,row in enumerate(L)])
assert len(pivots)==12 and all(c<24 for c in pivots)
solution=[0]*24
for j,c in enumerate(pivots):solution[c]=reduced[j][-1]
A=[clean(solution[8*j:8*(j+1)]) for j in range(3)]
assert max(map(len,A))<=8 and dot(A,w)==V
ca,ab=cross(C,A),cross(A,B);M=[[w[j],ca[j],ab[j]] for j in range(3)];N=[A,B,C]
for E,F in ((M,N),(N,M)):
    for i in range(3):
        for j in range(3):assert dot(E[i],[F[r][j] for r in range(3)])==(V if i==j else [0])
assert dot(M[0],cross(M[1],M[2]))==mul(V,V)
fg=[]
for row,f in zip(ci,W):
    Q=[dot([[a] for a in row],[M[r][j] for r in range(3)]) for j in range(3)]
    assert Q[0]==f;exact(V,f)
    fg.append([exact(Q[1],f),exact(Q[2],f)])
assert all(len(a)<=6 for pair in fg for a in pair)
u=[]
for x in base:
    owners=[i for i,f in enumerate(W) if ev(f,x)]
    vals=[tuple(ev(a,x) for a in fg[i]) for i in owners]
    assert owners and len(set(vals))==1;u.append(vals[0])
for i,(f,g) in enumerate(fg):
    for j,x in enumerate(base):
        e0,e1=(ev(f,x)-u[j][0])%P,(ev(g,x)-u[j][1])%P
        assert (e0==0 and e1==0)==(x not in roots[i])
        if e0 or e1:
            assert e1 and -e0*pow(e1,-1,P)%P==frame_gammas[i][roots[i].index(x)]

class F:
    __slots__=('a','b')
    def __init__(self,a=0,b=0):
        if isinstance(a,F):self.a,self.b=a.a,a.b
        else:self.a,self.b=a%P,b%P
    def __add__(self,o):
        o=F(o);return F(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return F(-self.a,-self.b)
    def __sub__(self,o):return self+-F(o)
    def __rsub__(self,o):return F(o)+-self
    def __mul__(self,o):
        o=F(o);return F(self.a*o.a-self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def inverse(self):
        assert self
        norm=(self.a*self.a+self.b*self.b)%P
        assert norm
        inv=pow(norm,-1,P);return F(self.a*inv,-self.b*inv)
    def __truediv__(self,o):return self*F(o).inverse()
    def __pow__(self,n):
        if n<0:return self.inverse()**(-n)
        y=F(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def __bool__(self):return bool(self.a or self.b)
    def __eq__(self,o):
        o=F(o);return self.a==o.a and self.b==o.b
    def __hash__(self):return hash((self.a,self.b))
    def pair(self):return [self.a,self.b]

assert pow(P-1,(P-1)//2,P)==P-1
assert all(F(a,b)*F(a,b).inverse()==1 for a in range(P) for b in range(P) if a or b)

def extension_rank(a):
    a=[[F(x) for x in row] for row in a];r=0
    for c in range(len(a[0])):
        pi=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pi is None:continue
        a[r],a[pi]=a[pi],a[r];iv=a[r][c].inverse();a[r]=[v*iv for v in a[r]]
        for i in range(r+1,len(a)):
            fac=a[i][c]
            if fac:a[i]=[x-fac*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r

def extension_ev(a,x):
    y=F(0)
    for c in a[::-1]:y=y*x+c
    return y

def compose_rho(a):
    y=[0];power=[1]
    for c in a:y=add(y,scale(power,c));power=mul(power,[2,0,1])
    return y

assert 2 not in base
nodes=[];base_index=[]
for j,a in enumerate(base):
    t=(a-2)%P
    sr=next((s for s in range(1,P) if s*s%P==t),None)
    if sr is not None:x=F(sr)
    else:
        si=next(s for s in range(1,P) if -s*s%P==t);x=F(0,si)
    assert x and x*x+2==a
    nodes.extend([x,-x]);base_index.extend([j,j])
assert len(set(nodes))==22
fullV=compose_rho(V);fullW=[compose_rho(f) for f in W]
fullB=[compose_rho(f) for f in B];fullC=[compose_rho(f) for f in C]
assert len(fullV)==23 and all(extension_ev(fullV,x)==0 for x in nodes)
assert cross(fullB,fullC)==[compose_rho(f) for f in w]
assert rank(coeff_map([compose_rho(f) for f in w],3))==12
assert all(len(f)==9 and exact(fullV,f) for f in fullW)
full_fg=[[compose_rho(f) for f in pair] for pair in fg]
assert all(len(f)<=11 for pair in full_fg for f in pair)
fullu=[tuple(F(v) for v in u[j]) for j in base_index]
full_cores=[]
for i,pair in enumerate(full_fg):
    core=[]
    for j,x in enumerate(nodes):
        vals=tuple(extension_ev(f,x) for f in pair)
        joint=vals==fullu[j]
        assert joint==bool(extension_ev(fullW[i],x))
        if joint:core.append(j)
    assert len(core)==14;full_cores.append(core)
proofs=[]
for i,(f,g) in enumerate(full_fg):
    for gamma in frame_gammas[i]:
        support=[j for j,x in enumerate(nodes) if extension_ev(f,x)+gamma*extension_ev(g,x)==fullu[j][0]+gamma*fullu[j][1]]
        assert len(support)==16 and set(full_cores[i])<=set(support)
        extras=sorted(set(support)-set(full_cores[i]));assert len(extras)==2
        assert base_index[extras[0]]==base_index[extras[1]]
        vand=[[nodes[j]**a for a in range(11)] for j in support]
        assert extension_rank(vand)==11
        aug=[extension_rank([row+[fullu[j][q]] for row,j in zip(vand,support)]) for q in (0,1)]
        assert aug==[12,12]
        decoder=add(f,scale(g,gamma));assert len(decoder)<=11
        assert all(extension_ev(decoder,nodes[j])==fullu[j][0]+gamma*fullu[j][1] for j in support)
        proofs.append(dict(pencil=i,gamma=gamma,support=support,extra_base_node=base[base_index[extras[0]]],augmented_ranks=aug))
assert len(proofs)==24 and len({r['gamma'] for r in proofs})==23
assert set.intersection(*(set(r) for r in roots))==set()
# Characteristic boundary for the literal integer frame and named base incidences.
def imul(a,b):
    y=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,z in enumerate(b):y[i+j]+=x*z
    return y

def isub(a,b):return [(a[j] if j<len(a) else 0)-(b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))]
iw=[isub(imul(B[(j+1)%3],C[(j+2)%3]),imul(B[(j+2)%3],C[(j+1)%3])) for j in range(3)]
ival=[]
for ci0,rs in zip(POINTS,EXPECTED_ROOTS):
    f=[sum(ci0[j]*iw[j][k] for j in range(3)) for k in range(5)]
    for x in rs:
        y=0
        for a in f[::-1]:y=y*x+a
        ival.append(y)
igcd=math.gcd(*ival)
assert len(ival)==24 and igcd==43
# Complete field-wide census, using the independently audited even-fiber reduction.
# On each eight-base-point support, take the two quotient syndromes modulo degree<=5.
census_witnesses={gamma:[] for gamma in range(P)}
joint_base_supports=0
census_supports=0
for support in itertools.combinations(range(11),8):
    census_supports+=1
    vand=[[pow(base[j],a,P) for a in range(6)] for j in support]
    reduced,ps=rr([row+[u[j][0],u[j][1]] for row,j in zip(vand,support)])
    assert ps[:6]==list(range(6))
    residual=[row[6:] for row in reduced[6:]]
    assert len(residual)==2
    if all(v==0 for row in residual for v in row):
        joint_base_supports+=1
        continue
    assert any(rank([row+[u[j][q]] for row,j in zip(vand,support)])==7 for q in (0,1))
    for gamma in range(P):
        if all((row[0]+gamma*row[1])%P==0 for row in residual):
            assert rank([row+[(u[j][0]+gamma*u[j][1])%P] for row,j in zip(vand,support)])==6
            census_witnesses[gamma].append(list(support))
assert census_supports==165
census_bad=[gamma for gamma,ss in census_witnesses.items() if ss]
assert census_bad==sorted(set(all_gammas))
assert len(census_bad)==23 and joint_base_supports==0
assert {g:len(census_witnesses[g]) for g in census_bad}=={g:(2 if g==29 else 1) for g in census_bad}
assert sum(map(len,census_witnesses.values()))==24
result=dict(status='PASS_INDEPENDENT_F43_QUADRATIC_SIX_MCA',prime=43,field_size=1849,extension='i^2=-1',rho=[2,0,1],
            base_basis=w,base_monic_locators=W,base_roots=roots,base_received=[list(a) for a in u],
            base_directions=frame_gammas,distinct_base_projective_directions=23,base_bezout_rank=12,
            base_bezout_row=A,base_pairs=fg,pullback_nodes=[x.pair() for x in nodes],
            full_pairs=full_fg,n=22,b=4,k=11,degree_cap=10,core_sizes=list(map(len,full_cores)),
            agreement_size=16,radius=[3,11],per_pencil_bad_counts=[4]*6,
            certified_distinct_bad_scalars=sorted(set(all_gammas)),bad_scalar_count=23,shared_gamma=29,
            original_MCA_nojoint_witnesses=proofs,checked_literal_integer_incidence_gcd=igcd,
            field_inverses_checked=1848,production_claim=False,all_bad_scalars_censused=True,
            full_field_MCA_census=dict(field_size=1849,base_scalars_checked=43,base_supports_checked=census_supports,
                                      scalar_support_checks=43*census_supports,joint_base_supports=joint_base_supports,
                                      bad_scalars=census_bad,bad_scalar_count=len(census_bad),
                                      qualifying_support_count_by_scalar={str(g):len(census_witnesses[g]) for g in census_bad},
                                      extra_scalars_beyond_six_pencils=sorted(set(census_bad)-set(all_gammas)),
                                      witness_base_supports={str(g):census_witnesses[g] for g in census_bad}))
print(json.dumps(result,indent=2))

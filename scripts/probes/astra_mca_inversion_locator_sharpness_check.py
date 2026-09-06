#!/usr/bin/env python3
"""Exact inversion-locator controls; no production witness or prize closure."""
import itertools,json,math
p=2013265921
def clean(a):
    a=[x%p for x in a]
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def add(a,b):return clean([(a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))])
def neg(a):return clean([-x for x in a])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return clean(c)
def ev(a,x):
    y=0
    for c in a[::-1]:y=(x*y+c)%p
    return y
def loc(xs):
    a=[1]
    for x in xs:a=mul(a,[-x,1])
    return a
def div(a,b):
    a=clean(a);q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);z=a[-1]*pow(b[-1],-1,p)%p;q[j]=z
        a=sub(a,[0]*j+[z*x for x in b])
    assert a==[0]
    return clean(q)
def dot(a,b):
    s=[0]
    for x,y in zip(a,b):s=add(s,mul(x,y))
    return s
def cross(a,b):return [sub(mul(a[(j+1)%3],b[(j+2)%3]),mul(a[(j+2)%3],b[(j+1)%3])) for j in range(3)]
def rref(a):
    a=[[x%p for x in row] for row in a];r=0;ps=[]
    for c in range(len(a[0])):
        pi=next((j for j in range(r,len(a)) if a[j][c]),None)
        if pi is None:continue
        a[r],a[pi]=a[pi],a[r];iv=pow(a[r][c],-1,p);a[r]=[v*iv%p for v in a[r]]
        for j in range(len(a)):
            if j!=r:
                fac=a[j][c];a[j]=[(x-fac*y)%p for x,y in zip(a[j],a[r])]
        ps.append(c);r+=1
        if r==len(a):break
    return a,ps
def rank(a):return len(rref(a)[1])
def coefficient_matrix(w,t):
    cols=[[0]*j+a for a in w for j in range(t+1)]
    h=max(map(len,cols))
    return [[a[i] if i<len(a) else 0 for a in cols] for i in range(h)]

assert all(p%d for d in range(2,math.isqrt(p)+1))
assert ev([p+1],2)==1
primitive=next(pow(a,(p-1)//10,p) for a in range(2,1000) if pow(pow(a,(p-1)//10,p),5,p)!=1 and pow(pow(a,(p-1)//10,p),2,p)!=1)
xs=[pow(primitive,j,p) for j in range(10)]
assert len(set(xs))==10 and loc(xs)==[p-1]+[0]*9+[1]

def det(mat):
    a=[[x%p for x in row] for row in mat];v=1
    for c in range(len(a)):
        row=next((r for r in range(c,len(a)) if a[r][c]),None)
        if row is None:return 0
        if row!=c:a[c],a[row]=a[row],a[c];v=-v
        v=v*a[c][c]%p;iv=pow(a[c][c],-1,p)
        for r in range(c+1,len(a)):
            f=a[r][c]*iv%p
            a[r]=[(x-f*y)%p for x,y in zip(a[r],a[c])]
    return v%p

G=[p-1,0,1];U=[p-1,0,0,0,1];J=[0,p-1,0,1]
V=loc(xs);fixed=[];first_ci=[]
for e in range(1,5):
    a=(xs[e]+xs[10-e])%p
    fixed.append(mul(G,loc([xs[e],xs[10-e]])))
    first_ci.append([1,-a%p,0])
records=[]
for choices in itertools.product((0,1),repeat=4):
    S=[e if bit==0 else 10-e for e,bit in zip(range(1,5),choices)]
    Sc=[10-e for e in S]
    H=loc([xs[e] for e in S]);Hr=loc([xs[e] for e in Sc]);c=H[0];ci=pow(c,-1,p)
    assert Hr==clean([a*ci for a in H[::-1]])
    w=[U,J,H]
    C=[[(-c)%p,0,p-1],[-H[1]%p,(c+1-H[2])%p,-H[3]%p],G]
    B=[[0,p-1],[1,0,1],[0]]
    assert cross(B,C)==w
    W=fixed+[H,Hr]
    coeff=first_ci+[[0,0,1],[((c-1)*ci)%p,((H[1]-H[3])*ci)%p,ci]]
    assert all(dot([[q] for q in row],w)==a for row,a in zip(coeff,W))
    rootsets=[{j for j,x in enumerate(xs) if ev(a,x)==0} for a in W]
    assert len({tuple(a) for a in W})==6 and all(len(r)==4 for r in rootsets)
    assert not set.intersection(*rootsets)
    overlaps=[[len(rootsets[i]&rootsets[j]) for j in range(6)] for i in range(6)]
    assert max(overlaps[i][j] for i in range(6) for j in range(i))==2
    assert all(overlaps[i][j]==1 for i in range(4) for j in (4,5)) and overlaps[4][5]==0
    assert rank([a+[0]*(5-len(a)) for a in W])==3
    longtrips=[a for a in itertools.combinations(range(6),3) if rank([coeff[i] for i in a])==2]
    assert longtrips==list(itertools.combinations(range(4),3))
    T=coefficient_matrix(w,1);td=det(T)
    assert len(T)==6 and td!=0
    L=coefficient_matrix(w,6)
    rr,ps=rref([row+[V[i] if i<len(V) else 0] for i,row in enumerate(L)])
    assert rank(L)==11 and all(i<21 for i in ps)
    solution=[0]*21
    for row,col in enumerate(ps):solution[col]=rr[row][-1]
    A=[clean(solution[j*7:(j+1)*7]) for j in range(3)]
    assert dot(A,w)==V
    ca,ab=cross(C,A),cross(A,B);M=[[w[i],ca[i],ab[i]] for i in range(3)];N=[A,B,C]
    for F,Z in ((N,M),(M,N)):
        for i in range(3):
            for j in range(3):assert dot(F[i],[Z[r][j] for r in range(3)])==(V if i==j else [0])
    fg=[]
    for i,row in enumerate(coeff):
        Q=[dot([[a] for a in row],[M[r][j] for r in range(3)]) for j in range(3)]
        assert Q[0]==W[i];div(V,W[i]);fg.append([div(Q[1],W[i]),div(Q[2],W[i])])
    assert all(len(a)<=5 for f in fg for a in f)
    u=[]
    for j,x in enumerate(xs):
        owners=[i for i,r in enumerate(rootsets) if j not in r];assert owners
        allv=[tuple(ev(a,x) for a in fg[i]) for i in owners]
        assert len(set(allv))==1;u.append(allv[0])
    residual=[]
    for i,(f,g) in enumerate(fg):
        rows=[((ev(f,x)-u[j][0])%p,(ev(g,x)-u[j][1])%p) for j,x in enumerate(xs)]
        assert all((row==(0,0))==(j not in rootsets[i]) for j,row in enumerate(rows))
        assert all(rows[j][1]==0 and rows[j][0]!=0 for j in rootsets[i]-{0,5}) if i<4 else True
        for j in rootsets[i]:
            e0,e1=rows[j];x=xs[j]
            if i<4 and j in (0,5):
                a=-coeff[i][1]%p
                numerator=(a*(1+c)+H[1]+H[3]-x*(1+c-H[2]))%p
                denominator=(a*x-2)%p
                assert e1 and denominator
                assert -e0*pow(e1,-1,p)%p==numerator*pow(denominator,-1,p)%p
            if i==4:
                assert e1 and -e0*pow(e1,-1,p)%p==(x+c*pow(x,-1,p))%p
            if i==5:
                assert e1 and -e0*pow(e1,-1,p)%p==(c*x+pow(x,-1,p))%p
        residual.append(rows)
    lam=next(t for t in range(25) if all((e1+t*e0)%p!=0 for rows in residual for e0,e1 in rows if e0 or e1))
    fg2=[[f,add(g,[lam*a for a in f])] for f,g in fg]
    u2=[(a,(b+lam*a)%p) for a,b in u]
    badsets=[];slotcounts=[];proofs=0
    for i,(f,g) in enumerate(fg2):
        core=[j for j in range(10) if j not in rootsets[i]];slots={}
        for j in rootsets[i]:
            e0,e1=residual[i][j];e1=(e1+lam*e0)%p
            assert e1;gamma=-e0*pow(e1,-1,p)%p
            slots.setdefault(gamma,[]).append(j)
        bad={ga for ga,js in slots.items() if len(js)>=2};badsets.append(bad);slotcounts.append(sorted(map(len,slots.values())))
        for gamma in bad:
            full=[j for j,x in enumerate(xs) if (ev(f,x)+gamma*ev(g,x)-u2[j][0]-gamma*u2[j][1])%p==0]
            exact=core+slots[gamma][:2];assert len(set(exact))==8
            assert set(full)==set(core)|set(slots[gamma])
            for support in (exact,full):
                vand=[[pow(xs[j],a,p) for a in range(5)] for j in support]
                assert rank(vand)==5
                assert any(rank([row+[u2[j][q]] for row,j in zip(vand,support)])==6 for q in (0,1))
            proofs+=1
    union=set.union(*badsets)
    assert len(set.intersection(*badsets[:4]))>=1
    assert list(map(len,badsets))==[1,1,1,1,0,0]
    assert slotcounts==[[1,1,2]]*4+[[1,1,1,1]]*2
    assert len(union)==1
    assert len(union)<=9<10
    records.append(dict(transversal_exponents=S,reciprocal_exponents=Sc,H_coefficients=H,
                        balance_determinant=td,bezout_rank=rank(L),pole_avoiding_shear=lam,
                        per_pencil_slot_multiplicities=slotcounts,per_pencil_bad_counts=list(map(len,badsets)),
                        union_bad_scalars=sorted(union),union_count=len(union),exact_and_full_support_nojoint_checks=proofs*2))
print(json.dumps(dict(status='PASS_INVERSION_FOUR_LINE_SHARPNESS',prime=p,trial_division_through=math.isqrt(p),
                     order10_generator=primitive,production_P_mod_5=365375409332725729550921208179070755120141565953%5,
                     b=2,n=10,all_16_transversals=records,total_pair_reconstructions=96,
                     total_exact_and_full_support_nojoint_checks=sum(r['exact_and_full_support_nojoint_checks'] for r in records),
                     distinct_union_counts=sorted({r['union_count'] for r in records}),
                     production_domain=False,dyadic_domain=False,over_budget=False),indent=2))

#!/usr/bin/env python3
"""Independent arithmetic audit of the five-pencil amplification.

Written independently of the original probe, with separate polynomial and
linear algebra routines and no imports from other repository probes.
The production argument remains a written proof, not a Lean formalization.
"""
import random
from math import isqrt, prod
import json
from itertools import combinations
P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
N=2**30
S=N//16
eta=pow(G,S,P)
z=eta*eta%P
assert pow(G,N,P)==1 and pow(G,N//2,P)==P-1
assert pow(eta,8,P)==P-1 and pow(z,4,P)==P-1

def tidy(a):
    a=[x%P for x in a]
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def plus(a,b):
    return tidy([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])

def times(a,b):
    v=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): v[i+j]=(v[i+j]+x*y)%P
    return tidy(v)

def scaled(a,c): return tidy([c*x for x in a])
def minus(a,b): return plus(a,scaled(b,-1))
def val(a,x):
    y=0
    for c in a[::-1]: y=(y*x+c)%P
    return y

def divrem(a,b):
    a=tidy(a);b=tidy(b);q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);c=a[-1]*pow(b[-1],-1,P)%P;q[j]=c
        a=minus(a,[0]*j+scaled(b,c))
    return tidy(q),a

def gcd(a,b):
    while b!=[0]: a,b=b,divrem(a,b)[1]
    return scaled(a,pow(a[-1],-1,P))

def interpolate(xs,ys):
    f=[0]
    for i,x in enumerate(xs):
        b=[1];den=1
        for j,y in enumerate(xs):
            if i!=j: b=times(b,[-y,1]);den=den*(x-y)%P
        f=plus(f,scaled(b,ys[i]*pow(den,-1,P)%P))
    return f

def elimination(mat):
    a=[row[:] for row in mat];rows=len(a);cols=len(a[0]);r=0;det=1;piv=[]
    for c in range(cols):
        pick=next((i for i in range(r,rows) if a[i][c]%P),None)
        if pick is None: continue
        if pick!=r: a[pick],a[r]=a[r],a[pick];det=-det
        pv=a[r][c]%P;det=det*pv%P;inv=pow(pv,-1,P)
        a[r]=[x*inv%P for x in a[r]]
        for i in range(rows):
            if i!=r and a[i][c]%P:
                factor=a[i][c]%P;a[i]=[(x-factor*y)%P for x,y in zip(a[i],a[r])]
        piv.append(c);r+=1
        if r==rows: break
    return r,det%P,piv,a

nodes=[pow(eta,j,P) for j in range(16)]
ls=[[pow(z,-i,P),0,pow(z,i,P)] for i in range(4)]
assign={3:2,11:2,4:1,12:1,5:0,13:1,6:0,14:0,7:0,15:0}
H=interpolate([nodes[j] for j in assign],[val(ls[i],nodes[j]) for j,i in assign.items()])
R=times(times([1,1],[-z,0,1]),[-z*z,0,1])
C=(1-z-z*z+pow(z,-1,P))%P
f=[times(R,l) for l in ls]+[times([0,0,C],times([1,1],[-z*z,0,1]))]
V=times(R,H)
cores=[{j for j in range(1,16) if val(V,nodes[j])==val(a,nodes[j])} for a in f]
assert [len(c) for c in cores]==[10]*4+[11]
assert all(sum(j in c for c in cores[:4])>=2 for j in range(1,16))

def matrix_for(deg, csets=cores[:4], xnodes=nodes):
    rows=[]
    for j in range(1,len(xnodes)):
        owners=[i for i,c in enumerate(csets) if j in c]
        for o in owners[1:]:
            row=[0]*((len(csets)-1)*(deg+1))
            for i,sgn in ((o,1),(owners[0],-1)):
                if i:
                    for a in range(deg+1): row[(i-1)*(deg+1)+a]=sgn*pow(xnodes[j],a,P)%P
            rows.append(row)
    return rows
rows=matrix_for(8)
rank,_,piv,_=elimination(rows)
minor=[[r[c] for c in range(25)] for r in rows]
mr,det,_,_=elimination(minor)
assert rank==mr==25 and piv==list(range(25))
assert det==96848988683743615843982839670225765648960583663
seeds=[minus(a,f[0]) for a in f[1:4]]
v=sum((a+[0]*(9-len(a)) for a in seeds),[])
yv=sum(([0]+a for a in seeds),[])
assert len(v)==len(yv)==27 and elimination([v,yv])[0]==2
assert all(sum(a*b for a,b in zip(r,w))%P==0 for r in rows for w in (v,yv))
Ws=[[0]]+[scaled(times([-z,1],[-pow(z,-i,P),1]),pow(z,i,P)-1) for i in range(1,4)]
Ws.append(scaled(times([-pow(z,6,P),1],[-pow(z,7,P),1]),-1))
Wg=Ws[1]
for a in Ws[2:]: Wg=gcd(Wg,a)
assert Wg==[1]
common=times([1,1],[-z*z,0,1])
for a,w in zip(f,Ws):
    sub=[0]*(2*len(w)-1)
    for j,c in enumerate(w):sub[2*j]=c
    assert minus(a,f[0])==times(common,sub)
for t in (1,z*z%P):assert len({val(w,t) for w in Ws[:4]})==4
prod_v=[S*(1-z*z)*val(w,1)%P for w in Ws]
assert len(set(prod_v))==5 and 1 not in prod_v
prod_gamma=[v*pow((1-v)%P,-1,P)%P for v in prod_v]
preimages=[None if ga==0 else pow(-pow(ga,-1,P)%P,N,P) for ga in prod_gamma]
assert all(a!=1 for a in preimages)

def lift(poly,s):
    a=[0]*(s*(len(poly)-1)+1)
    for i,x in enumerate(poly):a[s*i]=x
    return a

def dense(n):
    s=n//16;d=2*s;k=n//2;g=pow(G,N//n,P)
    xs=[pow(g,j,P) for j in range(n)]
    b=times([int(j%2==0) for j in range(d-1)],[-z*z]+[0]*(d-1)+[1])
    ps=[times(b,lift(w,d)) for w in Ws];qs=[[0]+a for a in ps]
    assert max(map(len,ps))==k-1 and max(map(len,qs))==k
    lift_f=[times([1]*s,lift(a,s)) for a in f]
    lift_V=times([1]*s,lift(V,s))
    old=[{j for j in range(1,n) if val(lift_V,xs[j])==val(a,xs[j])} for a in lift_f]
    kept=[c-{n//2} if i<4 else c for i,c in enumerate(old)]
    u0=[0]*n;u1=[0]*n
    for j in range(1,n):
        owners=[i for i,c in enumerate(kept) if j in c]
        assert owners
        vals=[val(ps[i],xs[j]) for i in owners]
        assert len(set(vals))==1
        u0[j]=vals[0];u1[j]=xs[j]*vals[0]%P
    hv=[val(a,1) for a in ps]
    for t in range(1,257):
        if t in hv:continue
        gammas=[v*pow((t-v)%P,-1,P)%P for v in hv]
        if len(set(gammas))==5 and all(ga==0 or pow(-pow(ga,-1,P)%P,n,P)!=1 for ga in gammas):break
    else:assert False
    u1[0]=t
    actual=[{j for j in range(n) if val(ps[i],xs[j])==u0[j] and val(qs[i],xs[j])==u1[j]} for i in range(5)]
    assert actual==kept
    witnesses={}
    for j in range(1,n):
        if val(b,xs[j])==0:continue
        i=next(i for i in range(5) if val(ps[i],xs[j])!=u0[j])
        ga=-pow(xs[j],-1,P)%P
        assert ga not in witnesses;witnesses[ga]=(i,j)
    assert len(witnesses)==12*s+1
    for i,ga in enumerate(gammas):assert ga not in witnesses;witnesses[ga]=(i,0)
    for ga,(i,extra) in witnesses.items():
        support=sorted(kept[i])[:11*s-2]+[extra]
        assert len(set(support))==11*s-1 and extra not in kept[i]
        decoder=plus(ps[i],scaled(qs[i],ga))
        assert len(decoder)<=k and all(val(decoder,xs[j])==(u0[j]+ga*u1[j])%P for j in support)
        # Independent augmented Vandermonde test of both rows on exactly this support.
        if n==16:
            vand=[[pow(xs[j],a,P) for a in range(k)] for j in support]
            ranks=[elimination([row+[u[j]] for row,j in zip(vand,support)])[0] for u in (u0,u1)]
            assert max(ranks)==k+1
        # On the first k core coordinates the only possible joint codewords are ps[i],qs[i].
        assert len(support)-1>=k
        assert val(ps[i],xs[extra])!=u0[extra] or val(qs[i],xs[extra])!=u1[extra]
    return {'n':n,'witness_count':len(witnesses),'core_sizes':[len(c) for c in kept],
            'zero_B_count':sum(val(b,x)==0 for x in xs),'hole_chart':t,
            'exact_support_size':11*s-1,'augmented_vandermonde_nojoint':n==16}

l=(S-1)//3;m=(4*S-1)//3
zero=4*S-1-(4*l)//3;unc=1+2*l;upper=N-zero+4*unc
assert 11*S-1-l==12*S-1-m==715827882
assert 4*l<2*S and 4*S-m-8*l==3
assert upper==1014089502 and N-upper==59652322
assert P//2**128==N and (12*S+6)*2**128<P
result={'independent':True,'repo_imports':False,'order_verified':N,
        'base_cores':[sorted(c) for c in cores],
        'degree_8_rank':rank,'first_25_column_determinant':det,
        'degree_kernel_nullities':{str(d):3*(d+1)-elimination(matrix_for(d))[0] for d in (6,7,8,9)},
        'primitive_gcd':Wg,'production_private_nth_powers':preimages,
        'production_certified_count':12*S+6,'production_radius':[5*S+1,N],
        'retained_ceiling':upper,'fifth_root_surplus':4*S-m-8*l,
        'forced_zeros':zero,'uncovered_bound':unc,'dense':[dense(n) for n in (16,64,256)]}

n=64;s=4;k=32
xs=[pow(G,(N//n)*j,P) for j in range(n)]
old=[{j for j in range(1,n) if j%16==0 or j%16 in c} for c in cores]
source=[]
for h in (0,1,3,7,8):
    rows=matrix_for(k-1+h,old[:4],xs)
    dim=3*(k+h)-elimination(rows)[0]
    if h<8:assert dim==h+1
    source.append({'h':h,'kernel_dimension':dim})
rng=random.Random(84714513)
patterns=[
    [{32} for i in range(4)]+[{2,3,4,6,7}],
    [{5},{13},{13},{5},{2,3,4,6,7}],
    [{32},{32},{32},{2},{32,2,3,4,6}],
]
for unused in range(12):
    patterns.append([{rng.choice(sorted(c))} for c in old[:4]]+[set(rng.sample(sorted(old[4]),5))])
records=[]
for drops in patterns:
    kept=[c-d for c,d in zip(old,drops)]
    matrix=matrix_for(k-1,kept,xs)
    forced=set()
    for j in range(1,n):
        owners=[i for i,c in enumerate(kept) if j in c]
        if len({val(Ws[i],pow(xs[j],2*s,P)) for i in owners})>1:forced.add(j)
    dim=4*k-elimination(matrix)[0]
    assert dim==4*s-len(forced)
    unseen=n-len(set().union(*kept))
    assert len(forced)>=14 and unseen<=3 and n-len(forced)+4*unseen<=62
    records.append({'drops':[sorted(c) for c in drops],'dim':dim,'forced':len(forced),'uncovered':unseen})
assert [row['kernel_dimension'] for row in source] == [1,2,4,8,11]
result['full_first_four_descent_controls']=source
result['five_pencil_removal_controls']=records

certs={10455338053:(5,{2:2,3:2,223:1,829:1,1571:1}),462478642316479903:(3,{2:1,3:1,479:1,15391:1,10455338053:1}),P:(3,{2:36,7:3,26407:1,279991:1,4533259:1,462478642316479903:1})}
seen=set()
def certify(q):
    if q in seen:return
    if q not in certs:
        assert q>=2 and all(q%d for d in range(2,isqrt(q)+1));seen.add(q);return
    a,fac=certs[q]
    assert prod(p**e for p,e in fac.items())==q-1
    for p in fac:certify(p)
    assert pow(a,q-1,q)==1
    assert all(pow(a,(q-1)//p,q)!=1 for p in fac)
    seen.add(q)
certify(P)
result['Lucas_primality_certified']=P
result['certified_subprimes']=sorted(seen)

result['status']='PASS_INDEPENDENT_FIVE_PENCIL_AUDIT'
print(json.dumps(result,indent=2,sort_keys=True))

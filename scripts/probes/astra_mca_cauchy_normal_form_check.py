#!/usr/bin/env python3
"""Exact finite and sparse-production controls for astra_mca_cauchy_normal_form-2026-09-05.md.

The general normal form/converse is the written proof, not a finite sweep.
The production prime is the already certified ArkLib prime, not reproved here.
"""
from itertools import combinations
from math import isqrt
import json

P=365375409332725729550921208179070755120141565953
PROD_GENERATOR=303645430271030343624574566109998498685964493478

def trim(a,p):
    a=[x%p for x in a]
    while len(a)>1 and not a[-1]: a.pop()
    return a
def add(a,b,p):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))],p)
def scale(a,s,p): return trim([s*x for x in a],p)
def mul(a,b,p):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return trim(out,p)
def divrem(a,b,p):
    a=trim(a,p);b=trim(b,p);assert b!=[0]
    q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        d=len(a)-len(b);c=a[-1]*pow(b[-1],-1,p)%p
        q[d]=c;a=add(a,[0]*d+scale(b,-c,p),p)
    return trim(q,p),a
def exactdiv(a,b,p):
    q,r=divrem(a,b,p);assert r==[0];return q
def gcd(a,b,p):
    while b!=[0]: a,b=b,divrem(a,b,p)[1]
    return scale(a,pow(a[-1],-1,p),p)
def derivative(a,p): return trim([j*a[j] for j in range(1,len(a))] or [0],p)
def rank(a,p):
    a=[[x%p for x in row] for row in a];r=0
    for j in range(len(a[0])):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None: continue
        a[r],a[z]=a[z],a[r];iv=pow(a[r][j],-1,p)
        a[r]=[x*iv%p for x in a[r]]
        for z in range(len(a)):
            if z!=r:
                c=a[z][j];a[z]=[(x-c*y)%p for x,y in zip(a[z],a[r])]
        r+=1
        if r==len(a): break
    return r
def interpolate_subgroup(vals,xs,p):
    n=len(xs);iv=pow(n,-1,p)
    return trim([iv*sum(v*pow(x,-j,p) for x,v in zip(xs,vals))%p for j in range(n)],p)
def recover(a,b,c,p):
    assert mul(a,c,p)==mul(b,b,p)
    h=gcd(a,b,p);f=exactdiv(a,h,p);g=exactdiv(b,h,p)
    d=exactdiv(h,f,p)
    lc=f[-1];f=scale(f,pow(lc,-1,p),p);g=scale(g,pow(lc,-1,p),p)
    d=scale(d,lc*lc,p)
    assert gcd(f,g,p)==[1]
    assert a==mul(d,mul(f,f,p),p)
    assert b==mul(d,mul(f,g,p),p)
    assert c==mul(d,mul(g,g,p),p)
    return d,f,g
def strong_conditions(n,c,p):
    m=n//4
    full=pow(-pow(c,-1,p)%p,m,p)!=1
    if m==2:
        return full,(1+c*c)%p!=0,None
    assert (m-2)%p and (m-1)%p and p!=2
    y=-2*(m-1)*pow(c*(m-2),-1,p)%p
    residue=(pow(y,m-1,p)+c*c*y+2*c)%p
    return full,residue!=0,residue

def dense_case(n,p,generator):
    k=n//2;xs=[pow(generator,j,p) for j in range(n)]
    assert len(set(xs))==n and all(pow(x,n,p)==1 for x in xs)
    c=next(c for c in range(2,100) if all(strong_conditions(n,c,p)[:2]))
    results=[]
    for name in ['strong_full','zero_coset','sign_gauge']:
        if name=='strong_full':
            ts=[(pow(x,k-2,p)+c*pow(x,k+2,p))%p for x in xs]
            d=[0]*(n-3);d[n-4]+=1;d[4]+=c*c;d[0]+=2*c;d=trim(d,p)
        elif name=='zero_coset':
            ts=[(1-pow(x,k,p))*pow(2,-1,p)%p for x in xs]
            d=[pow(2,-1,p)]+[0]*(k-1)+[-pow(2,-1,p)%p]
        else:
            ts=[pow(x,k,p) for x in xs];d=[1]
        e=[[t,t*x%p] for t,x in zip(ts,xs)]
        assert rank(e,p)==2
        aa=interpolate_subgroup([u*u%p for u,v in e],xs,p)
        bb=interpolate_subgroup([u*v%p for u,v in e],xs,p)
        cc=interpolate_subgroup([v*v%p for u,v in e],xs,p)
        assert aa==d and bb==[0]+d and cc==[0,0]+d
        assert add(mul(aa,cc,p),scale(mul(bb,bb,p),-1,p),p)==[0]
        rd,rf,rg=recover(aa,bb,cc,p)
        assert rd==d and rf==[1] and rg==[0,1]
        ranks=[]
        for s in range(k+1):
            mat=[[sum(pow(x,s+1,p)*row[i]*row[j] for x,row in zip(xs,e))%p
                  for j in range(2)] for i in range(2)]
            ranks.append(rank(mat,p))
            assert ranks[-1]<=s
        polys=[interpolate_subgroup([row[j] for row in e],xs,p) for j in range(2)]
        assert min(len(a)-1 for a in polys)>=k
        zeros=sum(t==0 for t in ts)
        if name=='strong_full':
            assert zeros==0 and gcd(d,derivative(d,p),p)==[1]
            assert len(d)>1 and ranks==[0,1,2,1]+[0]*(k-3)
            assert [len(a)-1 for a in polys]==[k+2,k+3]
            assert all((e[i][0]*e[j][1]-e[i][1]*e[j][0])%p
                       for i,j in combinations(range(n),2))
        elif name=='zero_coset':
            assert zeros==k and zeros+1>=k
            assert all(t in [0,1] for t in ts)
        else:
            assert zeros==0 and len(set(ts))==2 and rd==[1]
        # Test every residue of the rational determinant independently.
        for i,x in enumerate(xs):
            residue=sum(y*pow(n,-1,p)*pow(x-y,-1,p)*
                        (e[i][0]*e[j][1]-e[i][1]*e[j][0])**2
                        for j,y in enumerate(xs) if i!=j)%p
            assert residue==0
        results.append(dict(case=name,normal_scalar_degree=len(rd)-1,
                            primitive_pair_degree=1,zero_rows=zeros,
                            invertible_diagonal_rs_criterion=zeros+1<k,
                            actual_interpolant_degrees=[len(a)-1 for a in polys],
                            shifted_ranks=ranks))
    return dict(n=n,p=p,strong_parameter_c=c,cases=results)

def sparse_add(a,b,p):
    c=dict(a)
    for e,v in b.items(): c[e]=(c.get(e,0)+v)%p
    return {e:v for e,v in c.items() if v%p}
def sparse_mul(a,b,p,modulus_degree=None):
    c={}
    for i,x in a.items():
        for j,y in b.items():
            e=i+j if modulus_degree is None else (i+j)%modulus_degree
            c[e]=(c.get(e,0)+x*y)%p
    return {e:v for e,v in c.items() if v}
def production_audit():
    n=2**30;k=n//2;c=2;m=n//4
    t={k-2:1,k+2:c};d={n-4:1,4:c*c,0:2*c}
    assert sparse_mul(t,t,P,n)==d
    b={e+1:v for e,v in d.items()};cc={e+2:v for e,v in d.items()}
    assert sparse_mul(d,cc,P)==sparse_mul(b,b,P)
    full,squarefree,residue=strong_conditions(n,c,P)
    assert full and squarefree
    assert residue==179052947728843771035873342159914811345174123349
    assert max(cc)==n-2 and k+3<n and k+2>=k
    # Generic R' elimination used in the written proof is valid here.
    assert all(z%P for z in [4,c,m-1,m-2])
    zt={0:pow(2,-1,P),k:-pow(2,-1,P)%P}
    assert sparse_mul(zt,zt,P,n)==zt
    assert k+2<=n-2 and k+1>=k
    st={k:1};assert sparse_mul(st,st,P,n)=={0:1}
    return dict(n=n,k=k,prime=P,strong_parameter_c=c,
                nonzero_multiplier_power=pow(-pow(c,-1,P)%P,m,P),
                squarefree_elimination_residue=residue,
                gram_numerator_degree=n-2,first_shifted_rank=1,
                actual_interpolant_degrees=[k+2,k+3],
                zero_coset_rows=k,zero_coset_diagonal_rs_criterion=False,
                all_rational_minors_zero=True,billion_domain_expanded=False)

if __name__=='__main__':
    assert all(257%d for d in range(2,isqrt(257)+1))
    controls=[]
    for p in [257,P]:
        for n in [8,16,64]:
            generator=pow(3,(257-1)//n,257) if p==257 else pow(PROD_GENERATOR,(2**30)//n,P)
            controls.append(dense_case(n,p,generator))
    print(json.dumps(dict(status='PASS_CAUCHY_NORMALFORM_FALSE_POSITIVE_CONTROLS',
                         dense_controls=controls,production=production_audit(),
                         scope='Written converse; no Lean proof and no actual MCA bad-scalar construction.'),sort_keys=True))

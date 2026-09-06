#!/usr/bin/env python3
"""Exact controls for the written reciprocal parity obstruction; no repository imports."""
import json
P=365375409332725729550921208179070755120141565953

def rank(a,p):
    a=[[x%p for x in row] for row in a];r=0
    for c in range(len(a[0])):
        j=next((j for j in range(r,len(a)) if a[j][c]),None)
        if j is None:continue
        a[r],a[j]=a[j],a[r];iv=pow(a[r][c],-1,p);a[r]=[v*iv%p for v in a[r]]
        for j in range(r+1,len(a)):
            f=a[j][c];a[j]=[(x-f*y)%p for x,y in zip(a[j],a[r])]
        r+=1
        if r==len(a):break
    return r

def polynomial(m,terms,p):
    a=[0]*(m+1)
    for j,v in terms:a[j]=(a[j]+v)%p
    return a

def reciprocal(a,c,p):
    m=len(a)-1
    assert m%2==0
    return [a[m-j]*pow(c,m-j-m//2,p)%p for j in range(m+1)]

def coefficient_map(w,b):
    columns=[]
    for f in w:
        for j in range(b):columns.append([0]*j+f+[0]*(b-1-j))
    return [list(a) for a in zip(*columns)]

def case(b,c,p,a):
    assert b%2==1 and b>=3
    m=2*b;cb=pow(c,b,p);cb1=pow(c,b-1,p)
    plus=polynomial(m,[(m,1),(0,cb)],p)
    middle=polynomial(m,[(b,1)],p)
    plus2=polynomial(m,[(m-1,1),(1,cb1)],p)
    minus=polynomial(m,[(m,1),(0,-cb)],p)
    minus2=polynomial(m,[(m-1,1),(1,-cb1)],p)
    w,signs={1:([plus,minus,minus2],[1,-1,-1]),
             2:([plus,middle,minus],[1,1,-1]),
             3:([plus,middle,plus2],[1,1,1])}[a]
    assert rank(w,p)==3
    for f,s in zip(w,signs):assert reciprocal(f,c,p)==[s*x%p for x in f]
    T=coefficient_map(w,b);rt=rank(T,p)
    assert rt<=3*b-abs(a-2)
    if a==2:assert rt==3*b
    # Check every basis column of reciprocal equivariance, including the c-normalization.
    for i,s in enumerate(signs):
        for j in range(b):
            lhs=reciprocal([row[i*b+j] for row in T],c,p)
            factor=s*pow(c,j-(b-1)//2,p)%p
            rhs=[factor*row[i*b+(b-1-j)]%p for row in T]
            assert lhs==rhs
    t=(b-1)//2
    assert (3*t+a,3*t+3-a)==((t+1)*a+t*(3-a),t*a+(t+1)*(3-a))
    return dict(b=b,c=c,prime=p,plus_dimension=a,matrix_size=3*b,rank=rt,
                nullity=3*b-rt,required_nullity_lower_bound=abs(a-2))

records=[case(b,c,p,a) for p in (3,5,7,P) for b in (3,11) for c in ((1,2) if p==5 else (1,5)) if c%p for a in (1,2,3)]
# Even b does not obey the obstruction: the (1,2) reciprocal type can be balanced.
b=2;w=[[1,0,0,0,1],[-1,0,0,0,1],[0,-1,0,1,0]]
assert rank(coefficient_map(w,b),P)==6
production=[]
for j in range(1,16):
    n=4**j;b=(n+2)//6
    assert 6*b-2==n and b%2==1
    t=(b-1)//2
    production.append(dict(n=n,b=b,target_eigen_dimensions=[3*t+2,3*t+1],
                           balanced_locator_eigen_dimensions=[2,1],
                           forbidden_type_12_domain_eigen_dimensions=[3*t+1,3*t+2]))
print(json.dumps(dict(status='PASS_RECIPROCAL_BALANCE_PARITY_CONTROLS',exact_matrix_cases=records,
                     even_b2_type12_rank=6,dyadic_degree_checks=production,
                     no_production_domain_enumeration=True,production_six_locator_exclusion=False),indent=2))

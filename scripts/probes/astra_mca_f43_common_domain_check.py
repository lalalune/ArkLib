#!/usr/bin/env python3
"""Exact F43^2 common-domain MCA example; not a production-field example."""
from itertools import combinations
from math import gcd as int_gcd
from functools import reduce
import json

P=43
B=[[10,18,19],[36,37,40],[17,0,9]]
C=[[6,32,1],[30,3,17],[9,12,20]]
POINTS=[(1,20,7),(1,39,12),(1,17,13),(1,31,20),(1,29,26),(1,42,30)]
ROOTS=[[1,20,22,36],[0,15,20,39],[20,29,34,42],
       [22,32,39,42],[1,15,29,32],[0,32,34,36]]
DIRECTIONS=[[30,29,38,19],[29,5,1,34],[32,40,6,7],
            [14,21,26,41],[2,17,9,28],[12,23,35,42]]


def trim(a):
    a=[x%P for x in a]
    while len(a)>1 and not a[-1]:a.pop()
    return a or [0]


def add(a,b,s=1):
    return trim([(a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])


def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)


def ev(a,x):
    v=0
    for c in reversed(a):v=(v*x+c)%P
    return v


def dot(a,b):
    v=[0]
    for x,y in zip(a,b):v=add(v,mul(x,y))
    return v


def cross(a,b):
    return [add(mul(a[(i+1)%3],b[(i+2)%3]),mul(a[(i+2)%3],b[(i+1)%3]),-1)
            for i in range(3)]


def divexact(a,b):
    a=trim(a);q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);s=a[-1]*pow(b[-1],-1,P)%P
        q[j]=s;a=add(a,[0]*j+[s*x%P for x in b],-1)
    assert a==[0]
    return trim(q)


def locator(roots):
    v=[1]
    for x in roots:v=mul(v,[-x,1])
    return v


def rank(a):
    a=[[x%P for x in row] for row in a];r=0
    for j in range(len(a[0])):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None:continue
        a[r],a[z]=a[z],a[r];inv=pow(a[r][j],-1,P)
        a[r]=[x*inv%P for x in a[r]]
        for z in range(r+1,len(a)):
            s=a[z][j];a[z]=[(x-s*y)%P for x,y in zip(a[z],a[r])]
        r+=1
        if r==len(a):break
    return r


def solve(rows,values):
    a=[[x%P for x in row]+[v%P] for row,v in zip(rows,values)]
    r=0;piv=[]
    for j in range(len(rows[0])):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None:continue
        a[r],a[z]=a[z],a[r];inv=pow(a[r][j],-1,P)
        a[r]=[x*inv%P for x in a[r]]
        for z in range(len(a)):
            if z!=r:
                s=a[z][j];a[z]=[(x-s*y)%P for x,y in zip(a[z],a[r])]
        piv.append(j);r+=1
        if r==len(a):break
    assert r==len(a)
    out=[0]*len(rows[0])
    for z,j in enumerate(piv):out[j]=a[z][-1]
    return out,r


def compose(f,rho):
    v=[0]
    for c in reversed(f):v=add(mul(v,rho),[c])
    return v


def fm(x,y):
    return ((x[0]*y[0]-x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P)


def fa(x,y):return ((x[0]+y[0])%P,(x[1]+y[1])%P)
def fs(c,x):return (c*x[0]%P,c*x[1]%P)


def fe(f,x):
    v=(0,0)
    for c in reversed(f):v=fa(fm(v,x),(c,0))
    return v


def expanded(rows):
    # Restrict an F43[i]-linear system, i^2=-1, to the base field F43.
    out=[]
    for row in rows:
        out.append([v[0] for v in row]+[-v[1]%P for v in row])
        out.append([v[1] for v in row]+[v[0] for v in row])
    return out


def integer_incidence_gcd():
    def ie(f,x):return sum(c*x**j for j,c in enumerate(f))
    values=[]
    for ci,roots in zip(POINTS,ROOTS):
        for x in roots:
            bv=[ie(f,x) for f in B];cv=[ie(f,x) for f in C]
            wv=[bv[(j+1)%3]*cv[(j+2)%3]-bv[(j+2)%3]*cv[(j+1)%3] for j in range(3)]
            values.append(sum(ci[j]*wv[j] for j in range(3)))
    g=reduce(int_gcd,map(abs,values))
    assert g==43
    return g


def main():
    production_b=178956971
    assert all(production_b%d for d in range(2,59))
    assert production_b==59*3033169
    assert 6*(2*production_b//59)==36398028
    ys=sorted(set().union(*map(set,ROOTS)))
    assert len(ys)==11 and 2 not in ys
    V=locator(ys);w=cross(B,C)
    assert [f[-1] for f in w]==[2,16,25]
    Ws=[dot([[x] for x in ci],w) for ci in POINTS]
    for W,roots in zip(Ws,ROOTS):
        assert len(W)==5
        assert trim([x*pow(W[-1],-1,P)%P for x in W])==locator(roots)
        divexact(V,W)
    assert not set.intersection(*map(set,ROOTS))
    assert rank([W for W in Ws])==3
    # Bound7, not6: this base domain has11nodes, while b_base=2 would use10.
    cols=[[0]*j+f for f in w for j in range(8)]
    mat=[[v[i] if i<len(v) else 0 for v in cols] for i in range(12)]
    coeff,bezout_rank=solve(mat,V)
    A=[trim(coeff[8*j:8*j+8]) for j in range(3)]
    assert dot(A,w)==V and bezout_rank==12
    assert A==[[18,24,32,24,8,23,29,22],[21,42,32],[0]]
    ca,ab=cross(C,A),cross(A,B)
    M=[[w[j],ca[j],ab[j]] for j in range(3)]
    assert dot(M[0],cross(M[1],M[2]))==mul(V,V)
    pairs=[]
    for ci,W in zip(POINTS,Ws):
        q=[dot([[x] for x in ci],[M[j][k] for j in range(3)]) for k in range(3)]
        assert q[0]==W
        pairs.append([divexact(q[1],W),divexact(q[2],W)])
        assert max(map(len,pairs[-1]))<=6
    u={}
    for y in ys:
        own=next(i for i,W in enumerate(Ws) if ev(W,y))
        u[y]=tuple(ev(f,y) for f in pairs[own])
        for i,W in enumerate(Ws):
            assert (tuple(ev(f,y) for f in pairs[i])==u[y])==(ev(W,y)!=0)
    for i,roots in enumerate(ROOTS):
        ds=[]
        for y in roots:
            e0=(ev(pairs[i][0],y)-u[y][0])%P
            e1=(ev(pairs[i][1],y)-u[y][1])%P
            assert e1
            ds.append(-e0*pow(e1,-1,P)%P)
        assert ds==DIRECTIONS[i] and len(set(ds))==4
    gammas=sorted(set().union(*map(set,DIRECTIONS)))
    assert len(gammas)==23 and sum(len(v) for v in DIRECTIONS)==24
    assert {g for g in gammas if sum(g in s for s in DIRECTIONS)>1}=={29}
    # Pullback rho=X^2+2, with all 22 roots explicitly in F43[i].
    assert pow(P-1,(P-1)//2,P)==P-1
    omega=[];owners=[]
    for y in ys:
        v=(y-2)%P
        real=next((x for x in range(1,P) if x*x%P==v),None)
        if real is not None:x=(real,0)
        else:
            imaginary=next(x for x in range(1,P) if -x*x%P==v)
            x=(0,imaginary)
        assert fa(fm(x,x),(2,0))==(y,0)
        omega.extend([x,fs(-1,x)]);owners.extend([y,y])
    assert len(omega)==len(set(omega))==22
    fullV=compose(V,[2,0,1]);fullWs=[compose(W,[2,0,1]) for W in Ws]
    assert len(fullV)==23 and all(fe(fullV,x)==(0,0) for x in omega)
    fullpairs=[[compose(f,[2,0,1]) for f in pair] for pair in pairs]
    assert all(max(map(len,pair))<=11 for pair in fullpairs)
    received=[[(u[y][q],0) for y in owners] for q in (0,1)]
    vand=[]
    for x in omega:
        row=[(1,0)]
        for j in range(10):row.append(fm(row[-1],x))
        vand.append(row)
    assert rank(expanded(vand))==22
    ambient=[row+[received[0][i],received[1][i]] for i,row in enumerate(vand)]
    assert rank(expanded(ambient))==26 # dimension13 over F43^2, quotientrank2
    core_sets=[];witnesses=[]
    for i,((f,g),W) in enumerate(zip(fullpairs,fullWs)):
        core=[j for j,x in enumerate(omega) if (fe(f,x),fe(g,x))==(received[0][j],received[1][j])]
        assert len(core)==14
        assert set(core)=={j for j,x in enumerate(omega) if fe(W,x)!=(0,0)}
        core_sets.append(set(core))
        for gamma in DIRECTIONS[i]:
            support=[j for j,x in enumerate(omega)
                     if fa(fe(f,x),fs(gamma,fe(g,x)))==fa(received[0][j],fs(gamma,received[1][j]))]
            assert len(support)==16 and set(core)<=set(support)
            design=expanded([vand[j] for j in support])
            base_rank=rank(design);assert base_rank==22
            augmented=[]
            for q in (0,1):
                rhs=[z for j in support for z in received[q][j]]
                augmented.append(rank([row+[v] for row,v in zip(design,rhs)]))
            assert augmented==[23,23] # original same-support no-joint
            rhs=[z for j in support for z in fa(received[0][j],fs(gamma,received[1][j]))]
            assert rank([row+[v] for row,v in zip(design,rhs)])==base_rank
            witnesses.append({"pencil":i,"gamma":gamma,"support":support,
                              "base_field_design_rank":base_rank,"base_field_augmented_ranks":augmented})
    assert all(len(set(range(22))-core_sets[i]-core_sets[j])==2
               for i,j in combinations(range(6),2))
    # Full-field completeness is proved in docs/kb/astra_mca_f43_common_domain_counterexample-2026-09-05.md
    # by the even-fiber
    # reduction. Here census all 43 scalars on all C(11,8)=165 base supports,
    # with a fresh six-node interpolation computation and two residual tests.
    census={gamma:[] for gamma in range(P)}
    support_count=0
    joint_base_supports=0
    for support in combinations(ys,8):
        support_count+=1
        matrix=[[pow(y,j,P) for j in range(6)] for y in support[:6]]
        interpolants=[solve(matrix,[u[y][q] for y in support[:6]])[0] for q in (0,1)]
        residuals=[[(ev(interpolants[q],y)-u[y][q])%P for q in (0,1)]
                   for y in support[6:]]
        joint=all(not v for row in residuals for v in row)
        joint_base_supports+=joint
        for gamma in range(P):
            if all((row[0]+gamma*row[1])%P==0 for row in residuals):
                census[gamma].append(list(support))
    assert support_count==165 and joint_base_supports==0
    census_bad=[gamma for gamma,supports in census.items() if supports]
    assert census_bad==gammas
    assert sum(map(len,census.values()))==24
    assert all(len(census[g])==(2 if g==29 else 1) for g in gammas)
    return {"status":"PASS_ACTUAL_F43_SQUARED_SIX_PENCIL_23_SCALARS",
            "field":"F43[i], i^2=-1","n":22,"k":11,"degree_cap":10,
            "exact_core_size":14,"agreement_threshold":16,
            "distinct_finite_scalars":gammas,"saturated_pencils":6,
            "only_scalar_overlap":29,"all_pairwise_absence_intersections":2,
            "base_B":B,"base_C":C,"configuration_points":POINTS,
            "base_locator_roots":ROOTS,"base_directions":DIRECTIONS,
            "base_Bezout_row":A,"base_Bezout_rank":bezout_rank,
            "base_polynomial_pairs":pairs,"domain_nodes":omega,
            "received_pair":received,"witnesses":witnesses,
            "literal_integer_incidence_gcd":integer_incidence_gcd(),
            "production_smallest_nontrivial_cover_degree_bound":59,
            "production_nonbirational_six_scalar_bound":36398028,
            "all_bad_scalars_censused":True,
            "full_field_MCA_census":{"field_size":1849,"base_scalars_checked":43,
                                     "base_supports_checked":support_count,
                                     "scalar_support_checks":P*support_count,
                                     "joint_base_supports":joint_base_supports,
                                     "exact_bad_scalar_count":len(census_bad),
                                     "bad_scalars":census_bad,
                                     "qualifying_base_supports":{str(g):census[g] for g in gammas}},
            "production_field_or_length_claim":False,
            "scope":"Exact arbitrary-domain small-characteristic MCA counterexample; not a production or subgroup counterexample."}


if __name__=='__main__':print(json.dumps(main(),indent=2))

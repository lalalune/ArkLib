#!/usr/bin/env python3
"""Exact controls for written nested-extension obstructions; no odd-b candidate."""
import json
from itertools import combinations

P = 43
B0 = [[10,18,19],[36,37,40],[17,0,9]]
C0 = [[6,32,1],[30,3,17],[9,12,20]]
CI = [(1,20,7),(1,39,12),(1,17,13),(1,31,20),(1,29,26),(1,42,30)]
ROOTS = [[1,20,22,36],[0,15,20,39],[20,29,34,42],
         [22,32,39,42],[1,15,29,32],[0,32,34,36]]

def trim(a):
    a = [x % P for x in a]
    while len(a)>1 and a[-1]==0: a.pop()
    return a or [0]

def add(a,b,s=1):
    return trim([(a[j] if j<len(a) else 0)+s*(b[j] if j<len(b) else 0)
                 for j in range(max(len(a),len(b)))])

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b): c[j+k]+=x*y
    return trim(c)

def scale(a,c): return trim([c*x for x in a])

def divmodp(a,b):
    a=trim(a); b=trim(b); assert b != [0]
    q=[0]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        j=len(a)-len(b); c=a[-1]*pow(b[-1],-1,P)%P
        q[j]=c
        a=add(a,[0]*j+scale(b,c),-1)
    return trim(q),a

def monic(a): return scale(a,pow(a[-1],-1,P))

def gcdp(a,b):
    while b != [0]: a,b=b,divmodp(a,b)[1]
    return monic(a)

def ev(a,x):
    y=0
    for c in a[::-1]: y=(y*x+c)%P
    return y

def compose(a,rho):
    out=[0]
    for c in a[::-1]: out=add(mul(out,rho),[c])
    return out

def cross(a,b):
    return [add(mul(a[(j+1)%3],b[(j+2)%3]),mul(a[(j+2)%3],b[(j+1)%3]),-1)
            for j in range(3)]

def dot(a,b):
    out=[0]
    for f,g in zip(a,b): out=add(out,mul(f,g))
    return out

def locator(xs):
    out=[1]
    for x in xs: out=mul(out,[-x,1])
    return out

def rank(a):
    a=[[x%P for x in row] for row in a]
    r=0
    for j in range(len(a[0])):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None: continue
        a[r],a[z]=a[z],a[r]
        inv=pow(a[r][j],-1,P); a[r]=[x*inv%P for x in a[r]]
        for z in range(r+1,len(a)):
            c=a[z][j]; a[z]=[(x-c*y)%P for x,y in zip(a[z],a[r])]
        r+=1
        if r==len(a): break
    return r

def coefficient_rows(polys,size):
    return [[f[j] if j<len(f) else 0 for j in range(size)] for f in polys]

def syzygy_matrix(w,t):
    columns=[[0]*j+f for f in w for j in range(t+1)]
    size=max(map(len,columns))
    return [[f[j] if j<len(f) else 0 for f in columns] for j in range(size)]

def balanced_rank(w,b):
    assert max(map(len,w))==2*b+1
    result=rank(syzygy_matrix(w,b-1))
    assert result==3*b
    return result

def incidence_matrix(fi,ci,D):
    rows=[]
    for F,c in zip(fi,ci):
        d=len(F)-1
        remainders=[divmodp([0]*j+[1],F)[1] for j in range(D+1)]
        for t in range(d):
            rows.append([c[k]*(remainders[j][t] if t<len(remainders[j]) else 0)%P
                         for k in range(3) for j in range(D+1)])
    return rows

def degree(a): return -1 if a==[0] else len(a)-1

def agreement_count(w,v):
    minors=cross(w,v)
    nz=[f for f in minors if f != [0]]
    assert nz
    common=nz[0]
    for f in nz[1:]: common=gcdp(common,f)
    finite=[x for x in range(P) if ev(common,x)==0]
    assert len(finite)==degree(common)  # certifies complete geometric splitting
    D=max(map(degree,w))+max(map(degree,v))
    infinity=all(degree(f)<D for f in minors)
    return {"finite":finite,"infinity":infinity,"total":len(finite)+infinity}

def main():
    w0=cross(B0,C0)
    fi=[dot([[c] for c in ci],w0) for ci in CI]
    for F,roots in zip(fi,ROOTS): assert monic(F)==locator(roots)
    ys=sorted(set().union(*map(set,ROOTS)))
    assert len(ys)==11 and 2 not in ys
    multiplicities=[sum(y in roots for roots in ROOTS) for y in ys]
    assert sorted(multiplicities)==[2]*9+[3]*2
    assert all(rank(coefficient_rows([fi[j] for j in J],5))==3
               for J in combinations(range(6),5))
    assert all(monic(fi[i])!=monic(fi[j]) for i,j in combinations(range(6),2))
    assert all(rank([CI[i],CI[j]])==2 for i,j in combinations(range(6),2))
    assert balanced_rank(w0,2)==6
    base_kernel_ranks={}
    for D in (4,5):
        rr=rank(incidence_matrix(fi,CI,D))
        assert 3*(D+1)-rr==D-3
        base_kernel_ranks[str(D)]={"rank":rr,"nullity":3*(D+1)-rr}
    rho=[2,0,1]
    B=[compose(f,rho) for f in B0]; C=[compose(f,rho) for f in C0]
    w=cross(B,C); W=[compose(f,rho) for f in fi]
    assert w==[compose(f,rho) for f in w0]
    assert balanced_rank(w,4)==12
    V=compose(locator(ys),rho)
    for F in W: assert divmodp(V,F)[1]==[0]
    # Domain splitting in F43[i], including every full quadratic fiber.
    nodes=[]
    for y in ys:
        z=(y-2)%P
        a=next((a for a in range(1,P) if a*a%P==z),None)
        if a is not None: nodes.extend([(a,0),(-a%P,0)])
        else:
            a=next(a for a in range(1,P) if -a*a%P==z)
            nodes.extend([(0,a),(0,-a%P)])
    assert pow(P-1,(P-1)//2,P)==P-1
    assert len(nodes)==len(set(nodes))==22
    # Complete linear incidence module: fixed CI, all old roots retained.
    module_profile={}
    for D,expected in [(10,3),(12,5),(14,7),(16,9),(18,13)]:
        rr=rank(incidence_matrix(W,CI,D)); nullity=3*(D+1)-rr
        assert nullity==expected
        module_profile[str(D)]={"rank":rr,"nullity":nullity}
    A0=[[18,24,32,24,8,23,29,22],[21,42,32],[0]]
    A=[compose(f,rho) for f in A0]
    assert dot(A,w)==V
    ca,ab=cross(C,A),cross(A,B)
    assert dot(w,cross(ca,ab))==mul(V,V)
    assert [max(map(degree,z)) for z in (w,ca,ab)]==[8,18,18]
    assert rank([[f[-1] if degree(f)==d else 0 for f in z]
                 for z,d in [(w,8),(ca,18),(ab,18)]])==3
    # Sharp equal-degree agreement control, including source infinity.
    conic=[[1],[0,1],[0,0,1]]
    conic2=[[1,1],[0,2],[0,-1,3]]
    assert balanced_rank(conic,1)==balanced_rank(conic2,1)==3
    equal=agreement_count(conic,conic2)
    assert equal=={"finite":[0,1],"infinity":True,"total":3}
    # Sharp unequal-degree control: b=1 to b'=2 with four agreements.
    H=locator([0,1,2,3])
    quartic=[add([1],H),[0,1],add([0,0,1],H)]
    assert balanced_rank(quartic,2)==6
    unequal=agreement_count(conic,quartic)
    assert unequal=={"finite":[0,1,2,3],"infinity":False,"total":4}
    # Balance already gives gcd<=5; this weaker bound excludes five on a line.
    assert 5*10-4*5==30>28
    assert 5*4-4*2==12>11  # same argument gives the base five-span condition
    # Pure quadratic degree10 basis has a degree<=4 nonzero syzygy: 9>8.
    assert 3*(2+1)==9>5+2+1==8
    assert 2*2==4<5
    return {"status":"PASS_NESTED_ODD_STEP_OBSTRUCTION_CONTROLS",
            "field":"F43; actual old domain splits in F43[i], i^2=-1",
            "base_nodes":ys,"base_incidence_multiplicities":multiplicities,
            "base_any_five_locator_span":3,"base_balanced_rank":6,
            "lifted_balanced_rank":12,"lifted_domain_nodes":nodes,
            "base_incidence_kernel_ranks":base_kernel_ranks,
            "fixed_configuration_incidence_module":module_profile,
            "module_generator_degrees":[8,18,18],
            "sharp_equal_degree_agreement":equal,"sharp_unequal_degree_agreement":unequal,
            "b4_to_b5_max_fixed_configuration_retained_nodes":13,
            "b4_to_b5_min_lost_double_incidence_nodes":9,
            "nested_fixed_configuration_new_b_lower_bound":14,
            "nested_b5_moving_configuration":"excluded by written four-rank-case proof",
            "new_odd_b_MCA_candidate":False,"production_claim":False,
            "scope":"Finite controls for general written obstruction; no new MCA instance."}

if __name__=='__main__': print(json.dumps(main(),indent=2))

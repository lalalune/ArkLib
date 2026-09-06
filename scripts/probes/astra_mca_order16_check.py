#!/usr/bin/env python3
"""Exact production-field degree-seven witness and dense same-support checks.

This is a constructive unsafe-radius certificate, not a universal safety bound
or a Lean theorem. All calculations here use integers and exact field arithmetic.
"""
import json
from fractions import Fraction

P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
N=2**30
ETA=pow(G,N//16,P)

def trim(a):
    a=[v%P for v in a]
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%P
    return trim(out)
def sub(a,b):
    return trim([(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def ev(a,x):
    z=0
    for v in reversed(a):z=(z*x+v)%P
    return z
def rem(a,b):
    a=trim(a)
    while a!=[0] and len(a)>=len(b):
        c=a[-1]*pow(b[-1],-1,P)%P;d=len(a)-len(b)
        for j,v in enumerate(b):a[d+j]=(a[d+j]-c*v)%P
        a=trim(a)
    return a
def gcd(a,b):
    while b!=[0]:a,b=b,rem(a,b)
    return [0] if a==[0] else [v*pow(a[-1],-1,P)%P for v in a]
def roots_poly(ids):
    out=[1]
    for j in ids:out=mul(out,[-pow(ETA,j,P),1])
    return out
def seeds():
    # Triple types: A=012, B=013, C=023, D=123.
    A=(0,5,13);B=(1,8,9);C=(3,11,12);D=(4,7,15)
    w1=roots_poly(A+B+(6,))
    base2=roots_poly(A+C)
    x0,x1=pow(ETA,4,P),pow(ETA,7,P)
    y0=ev(w1,x0)*pow(ev(base2,x0),-1,P)%P
    y1=ev(w1,x1)*pow(ev(base2,x1),-1,P)%P
    slope=(y1-y0)*pow(x1-x0,-1,P)%P
    w2=mul(base2,[(y0-slope*x0)%P,slope])
    base3=roots_poly(B+C+(10,))
    factor=ev(w1,x0)*pow(ev(base3,x0),-1,P)%P
    w3=[factor*v%P for v in base3]
    return [[0],w1,w2,w3]

W=seeds()
EXPECTED=[[[0,1,2],[3]],[[0,1,3],[2]],[[0],[1],[2],[3]],[[0,2,3],[1]],
          [[0],[1,2,3]],[[0,1,2],[3]],[[0,1],[2],[3]],[[0],[1,2,3]],
          [[0,1,3],[2]],[[0,1,3],[2]],[[0,3],[1,2]],[[0,2,3],[1]],
          [[0,2,3],[1]],[[0,1,2],[3]],[[0],[1],[2,3]],[[0],[1,2,3]]]

def seed_checks():
    assert pow(G,N,P)==1 and pow(G,N//2,P)==P-1
    assert pow(ETA,16,P)==1 and pow(ETA,8,P)==P-1
    assert [len(w)-1 for w in W]==[0,7,7,7]
    gg=[0]
    for w in W:gg=gcd(gg,w)
    assert gg==[1]
    parts=[]
    for j in range(16):
        vals={}
        for i,w in enumerate(W):vals.setdefault(ev(w,pow(ETA,j,P)),[]).append(i)
        parts.append(list(vals.values()))
    assert parts==EXPECTED
    pairs={}
    for i in range(4):
        for h in range(i):
            diff=sub(W[i],W[h])
            assert len(diff)-1==7
            ids=[j for j in range(16) if ev(diff,pow(ETA,j,P))==0]
            assert len(ids) in (6,7)
            assert rem(diff,roots_poly(ids))==[0]
            pairs[f'{h},{i}']={'root_exponents':ids,'degree':len(diff)-1}
    return {'polynomials':W,'partitions':parts,'pair_roots':pairs,'gcd':gg}

def counts(s):
    assert s%6==4
    t=(s-4)//6;a=4*t+2;b=t;n=16*s;k=8*s
    roots=a+2*b
    assert roots==s-2
    owners=[]
    for j,groups in enumerate(EXPECTED):
        if j not in (2,6,10,14):
            group=next(g for g in groups if len(g)==3)
            owners.append((j,group,s))
    owners.extend([(6,[0,1],s-b),(14,[2,3],s-b),(10,[0,3],s//2),(10,[1,2],s//2)])
    core=[roots+sum(m for j,ids,m in owners if i in ids) for i in range(4)]
    assert core==[68*t+44]*4
    covered=sum(m for _,_,m in owners);uncovered=s-a
    assert covered+uncovered+roots==n
    D=covered+4*uncovered
    assert D==n+4 and core[0]>=k
    delta=Fraction(n-core[0]-1,n)
    assert delta==Fraction(7,24)+Fraction(1,3*n)
    return {'n':n,'s':s,'k':k,'t':t,'roots_fiber2':a,'roots_fiber6_and14_each':b,
            'common_roots':roots,'core_sizes':core,'covered':covered,'uncovered':uncovered,
            'fresh_directions':4*uncovered,'bad_count':D,'support_size':core[0]+1,
            'delta':[delta.numerator,delta.denominator],'max_p_degree':roots+7*s,
            'max_q_degree':roots+7*s+1,'security_margin':D*2**128-P}

def restricted_dual(s):
    # Restricted to these four sources with one common factor and q_i=Xp_i.
    # This does not count additional decoder pencils or prove universal safety.
    beta=[7,4,4,7,4,7,4,4,4,4,4,7,7,7,4,4]
    assert sum(beta)==82
    for j,groups in enumerate(EXPECTED):
        assert len(groups)<=beta[j]
        for group in groups:
            assert 1+3*len(set(group)&{0,2})<=beta[j]
        assert 6<=beta[j]+2
    A=counts(s)['core_sizes'][0]
    assert (68*s-5)//6==A
    assert 82*s+2*(s-2)-6*A==16*s+4
    return {'candidate_weights':[3,0,3,0],'fiber_weights':beta,'root_bonus':2,
            'inequality':'D + 3(C0+C2) <= 82s + 2 deg B',
            'integer_core_bound_for_D_gt_n':A,'attained_direction_count':16*s+4}

def dense(s):
    c=counts(s);n=c['n'];k=c['k'];a=c['roots_fiber2'];b=c['roots_fiber6_and14_each'];A=c['core_sizes'][0]
    g=pow(G,N//n,P);xs=[pow(g,j,P) for j in range(n)]
    assert len(set(xs))==n and pow(g,n,P)==1 and pow(g,s,P)==ETA
    fibers=[list(range(j,n,16)) for j in range(16)]
    roots=fibers[2][:a]+fibers[6][:b]+fibers[14][:b]
    B=[1]
    for j in roots:B=mul(B,[-xs[j],1])
    assert len(B)-1==s-2
    ps=[]
    for w in W:
        comp=[0]*(s*(len(w)-1)+1)
        for j,v in enumerate(w):comp[j*s]=v
        pi=mul(B,comp);assert len(pi)-1<=k-2;ps.append(pi)
    pv=[[ev(pi,x) for x in xs] for pi in ps]
    assert {j for j in range(n) if all(pv[i][j]==0 for i in range(4))}==set(roots)
    roots=set(roots);u=[None]*n;covered=[];uncov=[]
    for j,ids in enumerate(fibers):
        for h,z in enumerate(ids):
            if z in roots:u[z]=(0,0)
            elif j==2:uncov.append(z)
            else:
                if j==6:owner=0
                elif j==14:owner=2
                elif j==10:owner=0 if h<s//2 else 1
                else:owner=next(group[0] for group in EXPECTED[j] if len(group)==3)
                value=pv[owner][z];u[z]=(value,xs[z]*value%P);covered.append(z)
    assert len(covered)==c['covered'] and len(uncov)==c['uncovered']
    used={0}|{-pow(x,-1,P)%P for x in xs};witnesses=[]
    for z in covered:
        i=next(i for i in range(4) if pv[i][z]!=u[z][0])
        witnesses.append((-pow(xs[z],-1,P)%P,i,z))
    # Received pair (v,xv+1) is off every local pair; each direction is a
    # nonconstant fractional-linear function of v. At most 4|used|+8
    # choices of v are forbidden. Since |used| <= 5n+1, P > 20n+12 suffices.
    assert P>20*n+12
    max_trial=0
    for z in uncov:
        assert len({pv[i][z] for i in range(4)})==4
        v=0
        while True:
            local=[]
            for i in range(4):
                num=(v-pv[i][z])%P;den=(xs[z]*num+1)%P
                if not den:break
                gamma=-num*pow(den,-1,P)%P
                if gamma in used:break
                local.append((gamma,i,z))
            if len(local)==4:break
            v+=1
        assert len({gamma for gamma,_,_ in local})==4
        max_trial=max(max_trial,v);u[z]=(v,(xs[z]*v+1)%P)
        used.update(gamma for gamma,_,_ in local);witnesses.extend(local)
    assert len(witnesses)==n+4 and len({g for g,_,_ in witnesses})==n+4
    cores=[{z for z,x in enumerate(xs) if u[z]==(pv[i][z],x*pv[i][z]%P)} for i in range(4)]
    assert [len(core) for core in cores]==[A]*4
    for gamma,i,z in witnesses:
        assert z not in cores[i]
        agreement={j for j,x in enumerate(xs) if (u[j][0]+gamma*u[j][1]-(1+gamma*x)*pv[i][j])%P==0}
        assert agreement==cores[i]|{z}
        # Any full-code joint pair on this same support equals (p_i,Xp_i)
        # on A>=k core points and hence as polynomials, contradicting z.
        assert u[z]!=(pv[i][z],xs[z]*pv[i][z]%P)
    return {'n':n,'k':k,'source_degree':7,'common_root_degree':len(B)-1,'core':A,
            'support_size':A+1,'exact_core_plus_one_checks':len(witnesses),
            'unique_finite_directions':len(witnesses),'max_greedy_trial':max_trial}

if __name__=='__main__':
    seed=seed_checks();production=counts(N//16)
    assert production['delta']==[313174699,N]
    assert P==N*(2**128+192)+1
    assert production['security_margin']>0
    assert P>4*(N+5)+1
    assert production['max_p_degree']<=production['k']-2
    assert production['max_q_degree']<production['k']
    result={'status':'PASS_EXACT_ORDER16_DEGREE7_PRODUCTION_CONSTRUCTION',
            'scope':'Exact production-prime construction and n64/n256 dense controls; not a universal safety theorem or a Lean proof.',
            'seed':seed,'production':production,'dense':[dense(4),dense(16)],
            'restricted_dual':restricted_dual(N//16)}
    print(json.dumps(result,indent=2))

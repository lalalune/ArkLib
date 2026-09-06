#!/usr/bin/env python3
"""Exact actual-domain global-root six-pencil construction and MCA controls."""
import json
from pathlib import Path
from collections import defaultdict

HERE=Path(__file__).parent
SEED=json.loads(HERE.joinpath('astra_mca_root_relocation_seed.json').read_text())
P=SEED['prime'];G=SEED['generator'];N=SEED['production_n'];F=SEED['polynomials']


def trim(f):
    while f and not f[-1]:f.pop()
    return f


def evaluate(f,x):
    z=0
    for c in reversed(f):z=(z*x+c)%P
    return z


def subtract(f,g):
    return trim([((f[i] if i<len(f) else 0)-(g[i] if i<len(g) else 0))%P
                 for i in range(max(len(f),len(g)))])


def multiply(f,g):
    out=[0]*max(0,len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a:
            for j,b in enumerate(g):
                if b:out[i+j]=(out[i+j]+a*b)%P
    return trim(out)


def divide(f,g):
    f=f[:];g=trim(g[:]);out=[0]*max(0,len(f)-len(g)+1)
    inv=pow(g[-1],-1,P)
    while f and len(f)>=len(g):
        j=len(f)-len(g);c=f[-1]*inv%P;out[j]=c
        for i,v in enumerate(g):f[i+j]=(f[i+j]-c*v)%P
        trim(f)
    return trim(out),f


def gcd(f,g):
    while g:f,g=g,divide(f,g)[1]
    return [c*pow(f[-1],-1,P)%P for c in f]


def base_data():
    eta=pow(G,N//16,P)
    vals=[[evaluate(f,pow(eta,j,P)) for i,f in enumerate(F)] for j in range(16)]
    partitions=[]
    for j in range(16):
        groups=defaultdict(list)
        for i,v in enumerate(vals[j]):groups[v].append(i)
        partitions.append(list(groups.values()))
    W=[subtract(f,F[0]) for f in F]
    d=W[1]
    for w in W[2:]:d=gcd(d,w)
    assert d==[1]
    assert all(len(w)<=8 for w in W)
    assert len(partitions[0])==6 and all(len(g)>=2 for g in partitions)
    return W,partitions


def allocation(s,partitions):
    assert s%6==4 and s>=64
    a=(4*s+11)//20;A=21*s//2-2+a
    # States are tag, owner set, count. B has a root exactly in Z states.
    rows={j:[('C',max(partitions[j],key=len),s)] for j in range(16)}
    rows[0]=[('Z',list(range(6)),3*a-2),('C',[5],a),('U',[],s-4*a+2)]
    rows[12]=[('Z',list(range(6)),s-3*a),('C',[0],a),
              ('C',[1,3],a),('C',[2,4],a)]
    rows[14]=[('C',[0,2,3],s//2),('C',[1,4,5],s//2)]
    assert all(sum(c for tag,owners,c in row)==s and all(c>=0 for tag,owners,c in row)
               for row in rows.values())
    assert all(tag!='C' or owners in partitions[j]
               for j,row in rows.items() for tag,owners,c in row)
    cores=[0]*6;zeros=0;uncovered=0;capacity=0
    for j,row in rows.items():
        for tag,owners,c in row:
            for i in owners:cores[i]+=c
            zeros+=c*(tag=='Z');uncovered+=c*(tag=='U')
            capacity+=c*(len(partitions[j]) if tag=='U' else int(tag=='C'))
    assert zeros==s-2 and uncovered==s-4*a+2
    assert cores==[A]*6
    assert capacity==20*s+12-20*a
    assert capacity>16*s
    return rows,cores,capacity


def choose_received(x,local,used,n):
    values=sorted(set(local));r=len(values)
    a=next(v for v in range(r+1) if v not in values)
    for b in range(10000):
        if b==x*a%P or any((x*v-b)%P==0 for v in values):continue
        gammas=[(a-v)*pow((x*v-b)%P,-1,P)%P for v in values]
        assert len(set(gammas))==r and all(gammas)
        if any(g in used or pow(-pow(g,-1,P)%P,n,P)==1 for g in gammas):continue
        used.update(gammas)
        return (a,b),[(g,local.index(v)) for g,v in zip(gammas,values)]
    raise AssertionError('Dense least-integer greedy scan exhausted')


def dense_control(s,W,partitions):
    n=16*s;k=8*s;a=(4*s+11)//20;A=21*s//2-2+a
    root=pow(G,N//n,P)
    assert pow(root,n,P)==1 and pow(root,n//2,P)!=1
    rows,expected,expected_count=allocation(s,partitions)
    coords=[];tags=[];owner_sets=[]
    for j in range(16):
        t=0
        for tag,owners,count in rows[j]:
            for _ in range(count):
                coords.append(pow(root,j+16*t,P));tags.append(tag);owner_sets.append(owners);t+=1
        assert t==s
    assert len(set(coords))==n
    B=[1]
    for x,tag in zip(coords,tags):
        if tag=='Z':B=multiply(B,[-x%P,1])
    assert len(B)-1==s-2 and B[-1]==1
    polys=[]
    for w in W:
        sub=[0]*((len(w)-1)*s+1) if w else []
        for j,c in enumerate(w):sub[j*s]=c
        p=multiply(B,sub)
        assert len(p)<=k-1
        polys.append(p)
    assert max(map(len,polys))-1==k-2
    assert max(len([0]+p)-1 for p in polys)==k-1
    local=[[evaluate(p,x) for p in polys] for x in coords]
    used=set();word=[];witnesses=[]
    for pos,(x,tag,owners) in enumerate(zip(coords,tags,owner_sets)):
        if tag=='Z':
            assert all(v==0 for v in local[pos])
            word.append((0,0))
        elif tag=='C':
            v=local[pos][owners[0]]
            assert [i for i,a in enumerate(local[pos]) if a==v]==owners
            word.append((v,x*v%P))
        else:
            assert len(set(local[pos]))==6
            received,new=choose_received(x,local[pos],used,n)
            word.append(received);witnesses.extend((g,i,pos) for g,i in new)
    cores=[[j for j,(x,(a,b)) in enumerate(zip(coords,word))
            if (a,b)==(local[j][i],x*local[j][i]%P)] for i in range(6)]
    assert list(map(len,cores))==expected
    for pos,(x,tag,(a,b)) in enumerate(zip(coords,tags,word)):
        if tag=='C':
            i=next(i for i,v in enumerate(local[pos]) if v!=a)
            gamma=-pow(x,-1,P)%P
            assert gamma not in used
            used.add(gamma);witnesses.append((gamma,i,pos))
    assert len(witnesses)==len(used)==expected_count>n
    # Check the entire scalar agreement support for every claimed witness.
    # The explicit k-point core forces any joint explaining pair to equal
    # (p_i,Xp_i); its nonzero residual at pos then rules that pair out.
    for gamma,i,pos in witnesses:
        support=[]
        for j,(x,(a,b)) in enumerate(zip(coords,word)):
            r0=(a-local[j][i])%P;r1=(b-x*local[j][i])%P
            if (r0+gamma*r1)%P==0:support.append(j)
        assert len(support)==A+1 and set(support)==set(cores[i])|{pos}
        a,b=word[pos];x=coords[pos]
        assert (a-local[pos][i])%P or (b-x*local[pos][i])%P
        assert len(cores[i])>=k
    return {'n':n,'k':k,'agreement_threshold':A+1,
            'exact_joint_cores':expected,'common_factor_degree':s-2,
            'source_pair_degrees':[k-2,k-1],
            'distinct_finite_MCA_scalars':expected_count,'margin_over_n':expected_count-n,
            'actual_whole_support_and_no_joint_checks':len(witnesses),'status':'PASS'}


def main():
    assert P==365375409332725729550921208179070755120141565953
    assert N==2**30 and pow(G,N,P)==1 and pow(G,N//2,P)!=1
    W,partitions=base_data()
    s=N//16
    rows,cores,count=allocation(s,partitions)
    assert count==1073741832 and count-N==8
    assert cores==[718064843]*6
    # Greedy field-size bound permits all six-class choices at production.
    assert P>42*N+43 and count*(1<<128)>P
    # Exact local potential certificate for the fixed primitive seed family.
    # This verifies every owner class, with no LP solver or numerical output.
    beta=[6,16,21,6,6,11,16,16,21,21,16,11,6,16,11,16]
    weighted_candidates={0,1,2,5}
    for j,groups in enumerate(partitions):
        assert len(groups)<=beta[j]  # uncovered, nonzero common factor
        assert all(1+5*len(set(group)&weighted_candidates)<=beta[j]
                   for group in groups)
        assert 20<=beta[j]+14  # common-factor root, all four cores agree
        assert 1<=beta[j]+14  # a common-factor root can instead be uncovered
    assert sum(beta)==216
    restricted_capacity=230*s-28-20*cores[0]
    assert restricted_capacity==count
    assert (214*s-29)//20==cores[0]
    assert 230*s-28-20*(cores[0]+1)==N-12
    result={'status':'PASS','production':{'n':N,'s':s,'k':N//2,
            'agreement_threshold':718064844,'radius_numerator':355676980,
            'exact_joint_cores':cores,'common_factor_degree':s-2,
            'distinct_finite_MCA_scalars':count,'margin_over_n':count-N,
            'exceeds_2_power_minus128_numerator':True,
            'fiber0_states':rows[0],'fiber12_states':rows[12],'fiber14_states':rows[14]},
            'fixed_seed_capacity_certificate':{
                'beta':beta,'weighted_candidates':sorted(weighted_candidates),
                'root_coefficient':14,'core_weight':5,
                'exact_capacity_at_constructed_core':restricted_capacity,
                'largest_integer_core_with_capacity_over_n':cores[0],
                'scope':'This fixed primitive seed family; not a universal MCA upper bound.'},
            'dense_controls':[dense_control(s,W,partitions) for s in (64,256)],
            'scope':'Explicit received-pair existence and actual same-support MCA witnesses; not a universal lower bound or full-list census.'}
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()

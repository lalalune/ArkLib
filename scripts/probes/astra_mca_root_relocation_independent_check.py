#!/usr/bin/env python3
"""Independent relocated-root polynomial construction and exact MCA control.

Stdlib only. The polynomial fixture is embedded; no external data or LP code.
Production statements use exact compressed counts, not a billion-node scan.
"""
from collections import defaultdict
import json

P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
N=2**30
POLYNOMIALS=[[21013949898147473983537680665153842593321561442, 21013949898147473983537680665153842593321561442, 241616374370439463213342467754976913628320808321, 241616374370439463213342467754976913628320808321, 220602424472291989229804787089823071034999246880, 220602424472291989229804787089823071034999246880, 1, 1], [125829621549097067457234094028236226857884909488, 125829621549097067457234094028236226857884909488, 346432046021389056687038881118059297892884156365, 346432046021389056687038881118059297892884156365, 197517887987333714126611752820526843075613533581, 197517887987333714126611752820526843075613533581, 18943363311336672863882327061011457227257409586, 18943363311336672863882327061011457227257409586], [18943363311336672863882327061011457227257409586, 18943363311336672863882327061011457227257409586, 2070586586810801119655353604142385366064151855, 2070586586810801119655353604142385366064151855, 218531837885481188110149433485680685668935095024, 218531837885481188110149433485680685668935095024, 125829621549097067457234094028236226857884909488, 125829621549097067457234094028236226857884909488], [0, 0, 241616374370439463213342467754976913628320808320, 241616374370439463213342467754976913628320808320, 199588474574144515246267106424669228441677685438, 199588474574144515246267106424669228441677685438], [244567222147505997944249974301582298305981161792, 160765500394703878454091241603653756634739375189, 227694445422980126200023000844713226444787904061, 15992515534270138132974820514406072549597056113, 59836924077588110775713545486169314400259871692, 337269438483890118597165313759026757117031347328, 246637808734316799063905327905724683672045313650, 244567222147505997944249974301582298305981161792], [273845024500934793564451120510690141732203414540, 339433065796860823521675090606113624818515790595, 303819211434974040605777923295615780522681257811, 70801530015938233950717510030291325244615036139, 202973678805535967811055620979453844633629612002, 261791311638679092638702561965308095336038134929, 191729278294446120333900219327358656980089655875, 300341285584412772204089721511405378469434978565]]
WHOLE_OWNERS={1: [0, 1, 2, 4], 2: [0, 1, 2, 3, 5], 3: [2, 3, 4], 4: [1, 3, 4], 5: [0, 5], 6: [0, 2, 3, 4, 5], 7: [0, 1, 3, 4, 5], 8: [0, 1, 2, 3, 5], 9: [0, 1, 2, 4, 5], 10: [0, 1, 2, 3, 4], 11: [2, 3, 4, 5], 13: [1, 2, 5], 15: [0, 1, 3, 4, 5]}


def ev(f,x):
    z=0
    for c in f[::-1]:z=(z*x+c)%P
    return z


def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a


def difference(a,b):
    return trim([((a[j] if j<len(a) else 0)-(b[j] if j<len(b) else 0))%P
                 for j in range(max(len(a),len(b)))])


def divide(a,b):
    a=a[:];q=[0]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);c=a[-1]*pow(b[-1],-1,P)%P;q[j]=c
        for h,z in enumerate(b):a[j+h]=(a[j+h]-c*z)%P
        trim(a)
    return trim(q),a


def gcd(a,b):
    while b!=[0]:a,b=b,divide(a,b)[1]
    z=pow(a[-1],-1,P)
    return [c*z%P for c in a]


def multiply(f,g):
    h=[0]*(len(f)+len(g)-1)
    for i,c in enumerate(f):
        for j,d in enumerate(g):h[i+j]=(h[i+j]+c*d)%P
    return trim(h)


def allocation(s,a):
    z0,z12,U=3*a-2,s-3*a,s-4*a+2
    assert min(z0,z12,U,a)>=0 and z0+z12==s-2 and s%2==0
    rows={j:[(s,grp)] for j,grp in WHOLE_OWNERS.items()}
    rows[0]=[(z0,list(range(6))),(a,[5]),(U,None)]
    rows[12]=[(z12,list(range(6))),(a,[0]),(a,[1,3]),(a,[2,4])]
    rows[14]=[(s//2,[0,2,3]),(s//2,[1,4,5])]
    assert set(rows)==set(range(16))
    cores=[0]*6
    for row in rows.values():
        assert sum(c for c,g in row)==s
        for count,group in row:
            if group:
                for i in group:cores[i]+=count
    assert cores==[21*s//2-2+a]*6
    assert 20*s+12-20*a==16*s-(s-2)-U+6*U
    return rows,cores,U


def dense_control(s,seed_a):
    n=16*s;k=n//2;rows,expected,U=allocation(s,seed_a)
    assert N%n==0
    root=pow(G,N//n,P)
    root_nodes=[pow(root,16*t,P) for t in range(3*seed_a-2)]
    root_nodes += [pow(root,12+16*t,P) for t in range(s-3*seed_a)]
    assert len(root_nodes)==len(set(root_nodes))==s-2
    common=[1]
    for x in root_nodes:common=multiply(common,[-x%P,1])
    assert len(common)-1==s-2 and common[-1]==1
    ps=[]
    for f in POLYNOMIALS:
        W=difference(f,POLYNOMIALS[0])
        composed=[0]*((len(W)-1)*s+1)
        for j,c in enumerate(W):composed[j*s]=c
        p=multiply(common,composed)
        assert len(p)<=k-1
        ps.append(p)
    assert [len(p)-1 for p in ps]==[0]+[k-2]*5
    pairs={};sources={};core_counts=[0]*6;uncovered=[]
    ordinary={}
    node_count=0
    for j in range(16):
        assigned=[group for count,group in rows[j] for _ in range(count)]
        for t,group in enumerate(assigned):
            x=pow(root,j+16*t,P)
            assert x not in sources
            values=[ev(p,x) for p in ps]
            sources[x]=values;node_count+=1
            if group is None:
                uncovered.append(x)
                continue
            value=values[group[0]]
            assert [i for i,a in enumerate(values) if a==value]==group
            pairs[x]=(value,x*value%P)
            for i in group:core_counts[i]+=1
            absent=next((i for i,a in enumerate(values) if a!=value),None)
            if absent is not None:
                gamma=-pow(x,-1,P)%P
                assert gamma not in ordinary
                ordinary[gamma]=(absent,x)
    assert node_count==n and core_counts==expected
    assert len(ordinary)==n-(s-2)-U
    assert {x for x in sources if ev(common,x)==0}==set(root_nodes)
    assert len(uncovered)==U
    all_witnesses=dict(ordinary)
    # Every forbidden set is generated from exact previously used scalars.
    greedy=[]
    for x in sorted(uncovered):
        values=sources[x];distinct=set(values)
        assert len(distinct)==6
        poles={x*a%P for a in distinct}
        B=0
        while B in poles:B+=1
        forbidden={B*pow(x,-1,P)%P}
        for gamma in all_witnesses:
            for a in distinct:
                forbidden.add(((1+x*gamma)*a-gamma*B)%P)
        assert len(forbidden)<=len(distinct)*len(all_witnesses)+1<P
        A=0
        while A in forbidden:A+=1
        assert (B-x*A)%P!=0
        pairs[x]=(A,B)
        new=[]
        for a in distinct:
            gamma=(a-A)*pow((B-x*a)%P,-1,P)%P
            assert gamma not in all_witnesses and gamma not in new
            i=values.index(a)
            all_witnesses[gamma]=(i,x)
            new.append(gamma)
        greedy.append({'source':x,'rays':len(new),
                       'forbidden_values':len(forbidden),
                       'received_first':A,'received_second':B})
    assert len(all_witnesses)==20*s+12-20*seed_a and len(pairs)==n
    observed=[0]*6
    for x,(A,B) in pairs.items():
        for i,a in enumerate(sources[x]):
            observed[i]+=((A==a) and (B==x*a%P))
    assert observed==expected
    # Every listed gamma has its own actual outside agreement, in addition
    # to the exact joint core. A hypothetical joint pair on that support is
    # pinned by k core nodes and contradicts the nonzero residual here.
    for gamma,(i,x) in all_witnesses.items():
        A,B=pairs[x];a=sources[x][i];b=x*a%P
        assert (a,b)!=(A,B)
        assert (A+gamma*B-a-gamma*b)%P==0
        assert observed[i]>=k
    assert min(observed)+1==21*s//2-1+seed_a
    return {'n':n,'k':k,'s':s,'a':seed_a,'common_polynomial_degree':len(common)-1,
            'actual_common_domain_roots':len(root_nodes),'p_degrees':[len(p)-1 for p in ps],
            'q_degree_cap':k-1,'exact_joint_cores':observed,
            'event_agreement_threshold':min(observed)+1,
            'ordinary_distinct_rays':len(ordinary),
            'greedy_uncovered_coordinates':len(uncovered),
            'new_distinct_rays':sum(v['rays'] for v in greedy),
            'actual_distinct_MCA_witness_scalars':len(all_witnesses),
            'dense_source_polynomial_evaluations':6*n,
            'exact_outside_witness_checks':len(all_witnesses),
            'largest_forbidden_value_set':max(v['forbidden_values'] for v in greedy)}


def main():
    assert pow(G,N,P)==1 and pow(G,N//2,P)!=1
    eta=pow(G,N//16,P)
    diffs=[difference(f,POLYNOMIALS[0]) for f in POLYNOMIALS]
    d=diffs[1]
    for z in diffs[2:]:d=gcd(d,z)
    assert d==[1]
    base=[[ev(f,pow(eta,j,P)) for j in range(16)] for f in POLYNOMIALS]
    assert len({v[0] for v in base})==6
    partitions=[]
    for j in range(16):
        groups=defaultdict(list)
        for i,v in enumerate(base):groups[v[j]].append(i)
        partitions.append(list(groups.values()))
    assert all(len(z)>1 for z in partitions)
    # Direct dual verification; no LP optimizer is imported or trusted.
    weights=[5,5,5,0,0,5]
    fiber_y=[0,13,19,2,2,7,14,14,19,19,14,8,2,12,9,14]
    caps=[]
    for groups,y in zip(partitions,fiber_y):
        r=len(groups);cap=r+y;caps.append(cap)
        assert r<=cap
        assert all(1+sum(weights[i] for i in group)<=cap for group in groups)
        assert sum(weights)-14<=cap
    assert sum(caps)==216 and sum(weights)==20
    s=N//16;records=[]
    for a in ((s-4)//6+3,(s+1)//5):
        rows,cores,U=allocation(s,a)
        for j,row in rows.items():
            for count,group in row:
                if group is not None and group!=list(range(6)):
                    assert group in partitions[j]
        M=20*s+12-20*a
        assert M==sum(caps)*s+14*(s-2)-sum(weights)*cores[0]
        assert cores[0]>=N//2 and M>N and P>6*M+1
        security_margin=M*2**128-P
        assert security_margin>0
        records.append({'n':N,'s':s,'a':a,
            'common_roots_fiber0':3*a-2,
            'common_roots_fiber12':s-3*a,
            'B_degree':s-2,'p_degree_cap':8*s-2,'q_degree_cap':8*s-1,
            'exact_joint_core_sizes':cores,
            'full_agreement_threshold':cores[0]+1,
            'radius_numerator':N-cores[0]-1,'radius_denominator':N,
            'ordinary_distinct_scalars':N-(s-2)-U,
            'uncovered_coordinates':U,'fresh_distinct_scalars':6*U,
            'certified_distinct_MCA_scalars':M,'excess_above_security_budget':M-N,
            'strict_security_integer_margin':security_margin})
    assert records[0]['certified_distinct_MCA_scalars']==1118481032
    assert records[1]['certified_distinct_MCA_scalars']==1073741832
    assert records[1]['radius_numerator']==355676980
    controls=[dense_control(64,13),dense_control(256,51)]
    assert controls[0]['actual_distinct_MCA_witness_scalars']==1032
    assert controls[1]['actual_distinct_MCA_witness_scalars']==4112
    print(json.dumps({'status':'PASS_INDEPENDENT_RELOCATED_ROOT_MCA_WITNESSES',
         'base_difference_gcd':d,'base_partitions':partitions,
         'production_constructions':records,'dense_controls':controls,
         'direct_global_root_dual':{'candidate_weights':weights,'root_weight':14,
             'local_capacities':caps,'local_capacity_sum':sum(caps)},
         'scope':'Written production proof and exact controls; no billion-node enumeration, no full MCA census, no Lean formalization.'},indent=2))

if __name__=='__main__':main()

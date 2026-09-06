#!/usr/bin/env python3
"""Exact six-value certificate on the production subgroup; standard library only.

The adjacent JSON is exact input data. No LP solver or numerical result is used.
"""
import json
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
CERT=json.loads((HERE/'astra_mca_six_value_certificate.json').read_text())
P=CERT['prime'];G=CERT['generator'];N=CERT['production_n']

def ev(f,x):
    value=0
    for c in f[::-1]:value=(value*x+c)%P
    return value

def mul(f,g):
    out=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):out[i+j]=(out[i+j]+a*b)%P
    return out

def groups():
    out={j:[] for j in range(1,16)}
    for a in CERT['allocation']:
        out[a['base_exponent']].append((a['received_base_value'],Fraction(a['numerator'],a['denominator'])))
    assert all(sum((q for y,q in row),Fraction())==1 for row in out.values())
    assert all(q>0 for row in out.values() for y,q in row)
    return out

def rounded(groups,s):
    out={}
    for j,row in groups.items():
        used=0;out[j]=[]
        for h,(y,q) in enumerate(row):
            count=s-used if h==len(row)-1 else s*q.numerator//q.denominator
            used+=count;out[j].append((y,count))
        assert used==s and all(c>=0 for y,c in out[j])
    return out

def agreement_counts(base_values,alloc,s):
    return [s-1+sum(c for j,row in alloc.items() for y,c in row if values[j]==y)
            for values in base_values]

def dense_control(n,polys,allocs):
    assert n%16==0 and N%n==0
    s=n//16;k=n//2
    g=pow(G,N//n,P);eta=pow(g,s,P)
    vals=[[ev(f,pow(eta,j,P)) for j in range(16)] for f in polys]
    alloc=rounded(allocs,s)
    received={};owners={}
    for j,row in alloc.items():
        offset=0
        for value,count in row:
            for t in range(offset,offset+count):
                exponent=j+16*t;x=pow(g,exponent,P)
                J=(pow(x,s,P)-1)*pow(x-1,-1,P)%P
                received[exponent]=J*value%P;owners[exponent]=(j,value)
            offset+=count
    for t in range(1,s):received[16*t]=0
    assert len(received)==n-1
    full_polys=[]
    for f in polys:
        composed=[0]*((len(f)-1)*s+1)
        for j,c in enumerate(f):composed[j*s]=c
        full_polys.append(mul([1]*s,composed))
    expected=agreement_counts(vals,alloc,s)
    records=[]
    target=(2*n+2)//3+1  # punctured agreement ceil(2n/3), then include the hole
    for i,f in enumerate(full_polys):
        assert len(f)-1==s*len(polys[i])-1<k
        support=[j for j,y in sorted(received.items()) if ev(f,pow(g,j,P))==y]
        assert len(support)==expected[i]
        assert len(support)>=target-1
        # A k+1-row subsystem already obstructs any joint direction polynomial.
        short=support[:k]+[0]
        nodes=[pow(g,j,P) for j in short]
        weights=[]
        for x in nodes:
            den=1
            for y in nodes:
                if x!=y:den=den*(x-y)%P
            weights.append(pow(den,-1,P))
        powers=[1]*len(nodes)
        for d in range(k):
            assert sum(a*b for a,b in zip(weights,powers))%P==0
            powers=[a*b%P for a,b in zip(powers,nodes)]
        assert weights[-1]  # nonzero syndrome for the direction word at the hole
        records.append({'candidate':i,'degree':len(f)-1,'punctured_agreements':len(support),
                        'value_at_hole':ev(f,1),'same_support_no_joint_direction_syndrome':weights[-1]})
    assert len({r['value_at_hole'] for r in records})==6
    return {'n':n,'s':s,'records':records}

def main():
    assert P==365375409332725729550921208179070755120141565953
    assert N==2**30 and pow(G,N,P)==1 and pow(G,N//2,P)!=1
    eta=pow(G,N//16,P);assert pow(eta,16,P)==1 and pow(eta,8,P)!=1
    polys=CERT['polynomials'];assert len(polys)==6 and [len(f)-1 for f in polys]==[7,7,7,7,5,7]
    values=[[ev(f,pow(eta,j,P)) for j in range(16)] for f in polys]
    assert len({row[0] for row in values})==6
    allocs=groups()
    coverage=[]
    for j,row in allocs.items():
        for y,q in row:
            coverage.append({'base_exponent':j,'fraction':[q.numerator,q.denominator],
                             'candidates':[i for i,vals in enumerate(values) if vals[j]==y]})
    weighted=[sum((q for j,row in allocs.items() for y,q in row if vals[j]==y),Fraction()) for vals in values]
    assert weighted==[Fraction(49,5)]*4+[Fraction(51,5),Fraction(49,5)]
    s=N//16;k=N//2;target=715827883
    alloc=rounded(allocs,s);counts=agreement_counts(values,alloc,s)
    assert counts==[724775731,724775729,724775731,724775730,751619276,724775730]
    assert min(counts)>=target
    degrees=[s*len(f)-1 for f in polys]
    assert max(degrees)<k
    hole_values=[s*row[0]%P for row in values]
    assert len(set(hole_values))==6 and 2*hole_values[5]%P==hole_values[4]
    # Full old-word agreement census is recorded independently of its interpolation.
    old_word=[]
    owners={1:0,2:0,3:2,4:1,5:0,6:0,7:0,8:0,9:0,10:0,11:2,12:1,13:1,14:0,15:0}
    for j in range(16):old_word.append(values[owners.get(j,0)][j])
    old_agreements=[[j for j in range(1,16) if row[j]==old_word[j]] for row in values]
    assert old_agreements[5]==[1,3,4,6,7,9,10,11,15]
    assert list(map(len,old_agreements))==[10,10,10,10,11,9]
    return {'status':'PASS_EXACT_SIX_PRODUCTION_SINGLE_HOLE_VALUES',
            'prime':P,'generator':G,'base_eta':eta,'base_degree_cap':7,
            'base_values':values,'old_word_agreement_exponents':old_agreements,
            'allocation_coverage':coverage,'weighted_base_agreements':[str(q) for q in weighted],
            'production_n':N,'production_k':k,'production_agreement_requirement':target,
            'production_candidate_degrees':degrees,'production_punctured_agreements':counts,
            'production_agreement_slack':[a-target for a in counts],
            'production_values_at_hole':hole_values,
            'production_integer_allocations':{j:[{'value':y,'count':c} for y,c in row] for j,row in alloc.items()},
            'dense_controls':[dense_control(512,polys,allocs),dense_control(1024,polys,allocs)],
            'certified_production_value_count':6,'full_production_list_censused':False,
            'over_budget_claim':False,'scope':'Exact lower bound of six values, far below 2^30.'}

if __name__=='__main__':print(json.dumps(main(),indent=2))

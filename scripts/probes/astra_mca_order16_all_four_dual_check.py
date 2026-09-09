"""Independent exact local-dual/profile checks; does not rerun the field census."""
from pathlib import Path
from itertools import product, combinations
from fractions import Fraction
import argparse, json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("receipt", type=Path, help="Fresh output of astra_mca_order16_all_four_check.py")
args=parser.parse_args()
def partitions(n):
    if not n:
        yield [];return
    for ps in partitions(n-1):
        yield ps+[[n-1]]
        for i in range(len(ps)):
            yield [g+[n-1] if i==j else g[:] for j,g in enumerate(ps)]

states=0
for ps in partitions(4):
    t=int(any(len(g)==3 for g in ps));f=int(len(ps)==1)
    beta=8+3*t+4*f
    for g in ps:
        assert 2*int(len(ps)>1)+3*len(g)<=beta
        states+=1
    assert 2*len(ps)<=beta;states+=1  # uncovered node
    assert 12<=beta+4;states+=1       # common root

danger=[]
for f in range(8):
    for h in product(range(8),repeat=4):
        if tuple(sorted(h,reverse=True))!=h:continue
        if any(f+h[a]+h[b]>7 for a,b in combinations(range(4),2)):continue
        if 3*sum(h)+4*f>36:danger.append([f,list(h)])
assert danger==[[0,[4,3,3,3]],[1,[3,3,3,2]],[1,[3,3,3,3]]],danger

r=json.loads(args.receipt.read_text())
assert r['stats']['disjoint_unordered_B_C']==80080
assert r['stats']['ratio_tests']==3603600
assert r['stats']['ratio_equal_D_pairs']==8800
assert r['stats']['factor_assignments']==616000
assert r['stats']['triple_count_dual_prunes']==609280
assert r['stats']['has_thirteenth_required_triple']==0
assert r['stats']['has_quadruple']==6720
assert sum(r['unique_partition_uniform_upper_histogram'].values())==6720
profile_bounds=[]
for cert in r['exceptional_profile_certificates']:
    lam=Fraction(cert['lambda']);beta=list(map(Fraction,cert['beta']))
    z=Fraction(cert['root_extra']);profile=cert['profile']
    assert len(profile)==len(beta)==16 and z>=0 and lam>0
    for (m,classes),b in zip(profile,beta):
        assert b>=classes
        assert b>=int(classes>1)+lam*m
        assert b+z>=4*lam
    bound=(sum(beta)+z-16)/(4*lam)
    assert bound==Fraction(cert['bound']) and bound<=Fraction(67,6)
    profile_bounds.append(str(bound))

s=2**26;n=2**30
old_core=760567124
unexceptional_core_cap=(136*s-10)//12
exceptional_core_cap=(67*s)//6
assert unexceptional_core_cap==old_core
assert exceptional_core_cap<old_core
assert (n-old_core-1)==313174699
out={'status':'PASS_EXACT_LOCAL_DUAL_AND_REDUCTION_CONTROLS',
     'local_states_checked':states,'dangerous_sorted_profiles':danger,
     'exceptional_profile_bounds':profile_bounds,
     'unexceptional_integer_core_cap':unexceptional_core_cap,
     'exceptional_relaxed_integer_core_cap':exceptional_core_cap,
     'scope':'Exact independent checking of local/profile/integer reduction; field-census observations are read from its receipt, not independently regenerated here.'}
print(json.dumps(out,indent=2))

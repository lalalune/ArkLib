"""Bounded exact arithmetic checks; not a proof of the polynomial lemmas."""
import json

rows=[]
for s in [20,21,32,64,256,2**28]:
    n,k,t=4*s,2*s,3*s-1
    five_gap=5*t*t-n*(t+4*(k-1))
    hole_gap=4*t*t-(n-1)*(t+3*(k-1))
    defect_budget=6*(k-1)-12*t+6*n
    mixed_gap=(12*s-5)**2-(4*s-1)*(36*s-29)
    assert five_gap==s*s-10*s+5>0
    assert hole_gap==s>0
    assert defect_budget==6
    assert mixed_gap==32*s-4>0
    assert 3*s-19>k
    assert 3*(s+1)+2<=n
    # Coarse M bound from the exact source incidence constraints.
    for d in (0,1):
        for low in range(7):
            max_triple=(2*s-3-3*d+low)//2
            min_double=n-max_triple-low
            assert min_double>=3*s-7
    rows.append(dict(s=s,n=n,k=k,t=t,five_gap=five_gap,hole_gap=hole_gap,
        defect_budget=defect_budget,mixed_gap=mixed_gap,
        shared_double_core_min=3*s-19,polynomial_degree_max=k,
        two_exception_bound=3*(s+1)+2))
assert [r*(r-1)//2-3*r+6 for r in range(5)]==[6,3,1,0,0]
print(json.dumps({'scope':'Exact arithmetic only; polynomial arguments are written in the first-step note', 'rows':rows},indent=2))

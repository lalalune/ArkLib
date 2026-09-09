"""Exact global integer optimum for the uniform-list projective certificate."""
import json

n=2**30
s=n//4
t=3*s-1
e=n//2-1
mstar=n//18
m0=mstar+1

def gap(L,m):
    return (L+1)*(t-m)**2-(n-m)*(t-m+L*e)

assert gap(18,mstar)>0
assert 18*mstar+1<=n
assert 18*m0+1>n
# Any m>=m0 satisfying the budget has L<=17. For each such L,
# the gap is a convex quadratic in m, with positive coefficient L.
# Both endpoints m0 and t are negative, hence every m in [m0,t] fails.
endpoint_checks=[]
for L in range(1,18):
    assert gap(L,m0)<0
    assert gap(L,t)<0
    endpoint_checks.append(dict(L=L,gap_at_first_excluded_m=gap(L,m0),gap_at_t=gap(L,t)))

rows=[]
for L in range(1,101):
    # Feasibility can only lie before the first root: the quadratic
    # is negative at t and has positive leading coefficient.
    if gap(L,0)<=0:
        continue
    lo,hi=0,min(t-1,(n-1)//L)
    while lo<hi:
        mid=(lo+hi+1)//2
        if gap(L,mid)>0:
            lo=mid
        else:
            hi=mid-1
    rows.append(dict(L=L,m=lo,projective_bound=L*lo+1,gap=gap(L,lo)))
rows.sort(key=lambda x:x['m'],reverse=True)
assert rows[0]['L']==18 and rows[0]['m']==mstar
result=dict(n=n,k=n//2,t=t,required_support_range='0 <= m < t',
    global_optimal_m=mstar,attaining_L=18,attained_projective_bound=18*mstar+1,
    first_excluded_m=m0,budget_at_L18_first_excluded=18*m0+1,
    endpoint_certificate=endpoint_checks,largest_m_by_L=rows[:12])
print(json.dumps(result,indent=2))

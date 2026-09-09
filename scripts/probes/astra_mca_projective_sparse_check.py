"""Exact production arithmetic for projective-sparse.md, no dependencies."""
import json
from fractions import Fraction

P = 365375409332725729550921208179070755120141565953
n = 2**30
s,k,t = n//4,n//2,3*n//4-1
e = k-1
m = n//18

gap = 19*(t-m)**2-(n-m)*(t-m+18*e)
assert gap == 15*s*s-38*s+19-71*s*m+19*m+18*m*m > 0
assert Fraction(s*s-304*s+171,9) > 0
assert 18*m+1 == n-9
assert (18*m+1)*2**128 < P
assert n*2**128 < P < (n+1)*2**128

print(json.dumps({
    "n":n,"k":k,"support_threshold":t,
    "sparse_combination_radius":m,
    "punctured_list_bound":18,"johnson_positive_gap":gap,
    "projective_bad_bound":18*m+1,"finite_bad_bound":18*m+1,
    "integer_budget_slack":n-(18*m+1),
    "overbudget_necessary_minimum_distance":m+1,
    "bad_projected_word_maximum_distance":n-t,
    "security_numerator_margin":P-(18*m+1)*2**128,
    "infinity_counterexample":{
        "received_pair":"(0,X^k)","finite_bad_slots":[0],
        "swapped_pair":"(X^k,0)","swapped_finite_bad_slots":[],
        "projective_count_both":1,
        "verification":"written polynomial root-bound proof"}
},indent=2))

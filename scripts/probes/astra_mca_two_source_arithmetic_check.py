"""Exact finite arithmetic checks for two-source.md; no polynomial-lemma verification."""
import json
rows=[]
for s in [52,53,64,256,2**28]:
 n,k,t=4*s,2*s,3*s-1;r=t-1
 constant=5*r*r-n*(r+4*(k-1))
 rational=5*r*r-n*(r+4*k)
 assert constant==s*s-36*s+20>0
 assert rational==s*s-52*s+20>0
 assert 2*(s+1)+4<=n
 assert 2*(s+1)+(s+2)+2==3*s+6<=n
 for d in [0,1]:
  assert 2*t-(k-1-d)==n-1+d
 rows.append(dict(s=s,n=n,k=k,t=t,r=r,constant_list_gap=constant,
  rational_list_gap=rational,constant_bad_bound=2*s+6,
  linear_nonliftable_bad_bound=3*s+6))
print(json.dumps({'scope':'Exact arithmetic only; see the reviewed two-source written proof','rows':rows},indent=2))

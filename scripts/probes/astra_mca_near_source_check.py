"""Exact arithmetic checks for astra_mca_near_source-2026-09-08.md, not polynomial-lemma verification."""
import json
rows=[]
for s in [94,95,128,256,2**28]:
 n,k,t=4*s,2*s,3*s-1
 gap=5*(t-2)**2-n*((t-2)+4*(k+1))
 assert gap==s*s-94*s+45>0
 for d in [0,1,2]:
  assert t+(t-1)-(k-1-d)==n-2+d
 assert 3*s+8<=n
 assert 3*s+7<=n
 assert 9<=n
 R=t+3*(t-1);N=n-1;budget=6*(k-2)
 assert 2*R-3*N==budget+1
 rows.append(dict(s=s,n=n,k=k,t=t,rational_five_gap=gap,
  nonsaturating_bad_bound=3*s+8,strong_four_integer_gap=1))
assert all(r*(r-1)//2>=2*r-3 for r in range(5))
print(json.dumps({'checked_s':[x['s'] for x in rows],'production':rows[-1]}))

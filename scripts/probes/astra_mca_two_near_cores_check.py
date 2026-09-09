"""Exact finite incidence census and production arithmetic.
No polynomial realization is searched or certified here.
"""
import itertools,json
P=365375409332725729550921208179070755120141565953
edges=list(itertools.combinations(range(4),2))
def comps(total,length,prefix=()):
 if length==1:
  yield prefix+(total,)
 else:
  for a in range(total+1):yield from comps(total-a,length-1,prefix+(a,))
patterns={}
for label,doubles,singleton,quad in [('A',5,0,0),('B',3,1,0),('C',6,0,1)]:
 hits=[]
 for counts in comps(doubles,6):
  degrees=[sum(counts[j] for j,e in enumerate(edges) if i in e) for i in range(4)]
  # Triple-block size is s+offset; singleton owner is fixed as source 0.
  offsets=[1-doubles-singleton+degrees[i]+singleton*(i==0) for i in range(4)]
  slack=[]
  for j,(i,k) in enumerate(edges):
   opposite=[z for z in range(4) if z not in (i,k)]
   slack.append(-2-(offsets[opposite[0]]+offsets[opposite[1]]+counts[j]+quad))
  if min(slack)>=0:hits.append(dict(edge_counts=counts,triple_offsets=offsets,pair_slack=slack))
 patterns[label]=hits
assert [len(patterns[x]) for x in ['A','B','C']]==[6,1,1]
for h in patterns['A']:
 assert sorted(h['edge_counts'])==[0,1,1,1,1,1]
 assert sorted(h['triple_offsets'])==[-2,-2,-1,-1]
 assert sorted(h['pair_slack'])==[0,0,0,0,0,1]
assert patterns['B'][0]['edge_counts']==(0,0,0,1,1,1)
assert patterns['B'][0]['triple_offsets']==[-2,-1,-1,-1]
assert patterns['C'][0]['edge_counts']==(1,1,1,1,1,1)
assert patterns['C'][0]['triple_offsets']==[-2,-2,-2,-2]
rows=[]
for s in [136,137,256,2**28]:
 n,k,t=4*s,2*s,3*s-1
 gap=5*(t-3)**2-n*((t-3)+4*(k+2))
 assert gap==s*s-136*s+80>0
 assert 3*s+10<=n
 assert 2*(2*(t-1)+2*(t-2))-3*(n-1)==6*(k-3)+1
 assert 2*(4*(t-1))-3*(n-2)==6*(k-2)+2
 assert 5*(t-1)**2-n*((t-1)+4*(k-1))==s*s-36*s+20>0
 assert 5*(t-1)**2-(n-1)*((t-1)+4*(k-2))==s*s-9*s+10>0
 for typ,n1,n2,n4 in [('A',0,5,0),('B',1,3,0),('C',0,6,1)]:
  n3=n-1-n1-n2-n4
  assert n1+2*n2+3*n3+4*n4==4*(t-1)
  pairs=n2+3*n3+6*n4
  assert 6*(k-2)-pairs==int(typ=='A')
  assert 2*(k-2)-(n3+2*n4)==(1 if typ=='B' else 2)
 rows.append(dict(s=s,n=n,rational_list_gap=gap,forbidden_line_bound=4*n+1,
   conditional_bad_counts={'A_min':n+2,'B':n+3,'C':n+2}))
assert P>rows[-1]['forbidden_line_bound']
assert all(r*(r-1)//2>=2*r-3 for r in range(5))
out={'scope':'incidence and arithmetic only; no polynomial realization',
 'edge_order':edges,'patterns':patterns,'arithmetic':rows,
 'production_prime':P,'production_prime_exceeds_forbidden_line_bound':True}
print(json.dumps(out,indent=2))

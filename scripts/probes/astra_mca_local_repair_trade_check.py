#!/usr/bin/env python3
"""Exact finite certificate for membership-transition bounds, no field scan."""
from itertools import product
import json
unit=lambda j:tuple(int(i==j) for i in range(3))
zero=(0,0,0)
options=[]
for j in range(3):
 a=tuple(int(i!=j) for i in range(3))
 for target in (j,None):
  options.append((f'ordinary_missing_{j}_to_{target}',a,unit(j) if target is not None else zero))
for target in (1,2,None):
 options.append((f'private_A_to_{target}',unit(0),unit(target) if target is not None else zero))
assert len(options)==9
results={}
for r in (1,2):
 maxima={};two_lifts=[]
 for edits in product(options,repeat=r):
  a=tuple(sum(e[1][i] for e in edits) for i in range(3))
  b=tuple(sum(e[2][i] for e in edits) for i in range(3))
  delta=tuple(y-x for x,y in zip(a,b));q=tuple(r-x for x in b)
  L=sum(d>0 for d in delta)
  constant=sum(-d if d>0 else q[i]//(1-d) for i,d in enumerate(delta))+1
  maxima[L]=max(maxima.get(L,-99),constant)
  if L==2:
   assert r==2 and delta==(-2,1,1)
   assert {e[0] for e in edits}=={'private_A_to_1','private_A_to_2'}
   two_lifts.append([e[0] for e in edits])
 assert maxima==({0:3,1:1} if r==1 else {0:5,1:2,2:-1})
 results[r]={'state_tuples':len(options)**r,'max_constant_by_lifted_cores':maxima,'two_lift_transitions':two_lifts}
n=2**30;h=(n-4)//6;m=2*h+2;t=4*h+2;k=3*h+2;S=t+2
assert (n,k,t,S)==(1073741824,536870912,715827882,715827884)
assert 3*(m-1)==n-1
assert (m+1,2*m-2)==(357913943,715827882)
assert [h+1-r for r in (1,2)]==[178956970,178956969]
print(json.dumps({'status':'PASS','transition_certificate':results,'production':{'one_edit_old_pencil_bound':m+1,'two_edit_old_pencil_bound':2*m-2,'arbitrary_edits_old_pencil_bound':n-1,'core_omissions_to_escape_one_two_edits':[h,h-1]},'production_domain_enumerated':False},indent=2))

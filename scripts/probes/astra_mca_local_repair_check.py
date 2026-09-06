#!/usr/bin/env python3
"""Exact small controls for local repairs; no production-domain enumeration."""
from itertools import combinations
from collections import Counter
import json
import argparse
P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478

def trim(f):
 f=list(f)
 while len(f)>1 and not f[-1]:f.pop()
 return f

def add(f,g):
 return trim([((f[i] if i<len(f) else 0)+(g[i] if i<len(g) else 0))%P for i in range(max(len(f),len(g)))])
def scale(f,c):return trim([c*x%P for x in f])
def sub(f,g):return add(f,scale(g,-1))
def mul(f,g):
 h=[0]*(len(f)+len(g)-1)
 for i,x in enumerate(f):
  for j,y in enumerate(g):h[i+j]=(h[i+j]+x*y)%P
 return trim(h)
def ev(f,x):
 y=0
 for a in reversed(f):y=(y*x+a)%P
 return y

def interp(xs,ys):
 out=[0]
 for x,y in zip(xs,ys):
  f=[1];den=1
  for z in xs:
   if z!=x:f=mul(f,[-z%P,1]);den=den*(x-z)%P
  out=add(out,scale(f,y*pow(den,-1,P)%P))
 assert all(ev(out,x)==y for x,y in zip(xs,ys))
 return out

def divide(f,x):
 if f==[0]:return f
 q=[0]*(len(f)-1);carry=f[-1]
 for i in range(len(f)-2,-1,-1):q[i]=carry;carry=(f[i]+x*carry)%P
 assert carry==0
 q=trim(q);assert mul(q,[-x%P,1])==f
 return q

def label(e):
 if e==15:return 2
 while e%4==3:e//=4
 return e%4

def direction(v):
 a,b=v
 if not a and not b:return None
 return ('finite',-a*pow(b,-1,P)%P) if b else ('infinity',)

def fixture():
 g=pow(G,2**26,P);xs=[pow(g,e,P) for e in range(16)];i=pow(g,4,P)
 assert len(set(xs))==16 and i*i%P==P-1
 t=[0,0,0,0,1];q=add(t,[i]);j=pow(1-i,-1,P)
 h=interp(xs[3::4],[(i,i*pow(2,-1,P)%P,0)[label(e)] for e in range(3,16,4)])
 p0=scale(sub(t,[i]),j);q0=scale(sub([1],t),j)
 old0=[[0],mul(sub(t,[1]),add(p0,scale(h,1+i))),scale(mul(sub(t,[i]),sub(q0,scale(h,2))),-1)]
 old1=[[0],scale(mul(sub(t,[1]),q),1+i),scale(mul(sub(t,[i]),q),2)]
 a=ev(h,1)*pow(ev(q,1),-1,P)%P;b=ev(h,g)*pow(ev(q,g),-1,P)%P
 assert a!=b
 first=[divide(sub(f,scale(k,b)),g) for f,k in zip(old0,old1)]
 second=[divide(sub(f,scale(k,a)),1) for f,k in zip(old0,old1)]
 assert max(map(len,first+second))<=8
 aa,bb,cc=[{e for e in range(16) if label(e)==j}-{0,1} for j in range(3)]
 cores=[aa|bb|{0,1},aa|cc,bb|cc]
 vals=[[(ev(first[j],x),ev(second[j],x)) for x in xs] for j in range(3)]
 u=[next(vals[j][e] for j in range(3) if e in cores[j]) for e in range(16)]
 assert all({e for e in range(16) if vals[j][e]==u[e]}==cores[j] for j in range(3))
 assert list(map(len,cores))==[10]*3
 dirs=[direction(((u[e][0]-vals[j][e][0])%P,(u[e][1]-vals[j][e][1])%P)) for j in range(3) for e in range(16) if e not in cores[j]]
 assert len(dirs)==len(set(dirs))==18
 return xs,first,second,vals,u,cores

def projection_rows(xs,k=8,s=12):
 """Four explicit parity rows for each support; first eight are anchors."""
 out=[]
 for support in combinations(range(len(xs)),s):
  anchors=support[:k];rows=[]
  for j in support[k:]:
   x=xs[j];row={j:1}
   for a in anchors:
    num=den=1
    for b in anchors:
     if b!=a:num=num*(x-xs[b])%P;den=den*(xs[a]-xs[b])%P
    row[a]=-num*pow(den,-1,P)%P
   assert all(sum(c*pow(xs[e],d,P) for e,c in row.items())%P==0 for d in range(k))
   rows.append(row)
  out.append((support,rows))
 return out

def fixed_counts(u,vals,threshold=12):
 counts=[];union=set()
 for j in range(3):
  ds=Counter(direction(((u[e][0]-vals[j][e][0])%P,(u[e][1]-vals[j][e][1])%P)) for e in range(16))
  core=ds.pop(None,0)
  good={d for d,c in ds.items() if core+c>=threshold}
  # All cores retained here have >=k, so every counted nonzero residual
  # violates joint explanation by polynomial uniqueness, including infinity.
  assert core>=8
  counts.append((core,len(good)));union|=good
 return counts,union

def all_decoder_census(u,prepared,vals):
 """Exact projective scalar/support rank census, with original no-joint clause."""
 bad={};joint=0;outside_pencil_supports=0
 for support,rows in prepared:
  a=[sum(c*u[e][0] for e,c in row.items())%P for row in rows]
  b=[sum(c*u[e][1] for e,c in row.items())%P for row in rows]
  if not any(a) and not any(b):joint+=1;continue
  if not any(b):
   # Infinity decodes u1; u0 fails the joint condition.
   key=('infinity',)
  else:
   j=next(i for i,v in enumerate(b) if v)
   gam=-a[j]*pow(b[j],-1,P)%P
   if any((v+gam*w)%P for v,w in zip(a,b)):continue
   key=('finite',gam)
  if key[0]=='infinity':
   same=lambda j:all(u[e][1]==vals[j][e][1] for e in support[:8])
  else:
   same=lambda j:all((u[e][0]+key[1]*u[e][1]-vals[j][e][0]-key[1]*vals[j][e][1])%P==0 for e in support[:8])
  outside_pencil_supports+=int(not any(same(j) for j in range(3)))
  bad.setdefault(key,support)
 return bad,joint,outside_pencil_supports

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument("--verbose",action="store_true",help="include all 170 case records")
 args=parser.parse_args()
 xs,f,g,vals,u,cores=fixture();prepared=projection_rows(xs)
 base_bad,basejoint,baseoutside=all_decoder_census(u,prepared,vals)
 assert not base_bad
 # Every edit takes another local pair's vector at that coordinate.
 operations=[]
 for e in range(16):
  for v in sorted(set(vals[j][e] for j in range(3))-{u[e]}):operations.append((e,v))
 assert len(operations)==18
 changes=[()]+[(op,) for op in operations]+[(x,y) for x,y in combinations(operations,2) if x[0]!=y[0]]
 cases=[];maxima={0:0,1:0,2:0};new_decoders=[]
 for edits in changes:
  v=list(u)
  for e,w in edits:v[e]=w
  fixed,known=fixed_counts(v,vals)
  bad,joint,outside=all_decoder_census(v,prepared,vals)
  assert known<=set(bad)
  assert len(known)<=({0:1,1:6,2:10}[len(edits)])
  maxima[len(edits)]=max(maxima[len(edits)],len(bad))
  extra=set(bad)-known
  if extra:new_decoders.append({'edits':edits,'extra_count':len(extra),'one_direction':next(iter(extra)),'one_support':bad[next(iter(extra))]})
  cases.append({'edits':edits,'fixed_core_and_counts':fixed,'fixed_union':len(known),'all_projective_bad':len(bad),'new_decoder_count':len(extra),'joint_supports':joint,'outside_old_pencil_supports':outside})
 result={'status':'PASS','prime':P,'n':16,'k':8,'target':12,'old_projective_slots':18,'old_distinct_projective_directions':18,'support_projection_checks':len(prepared),'edit_cases':len(cases),'cases_by_edits':dict(Counter(len(x['edits']) for x in cases)),'maximum_all_decoder_bad_by_edit_count':maxima,'extra_bad_direction_cases':new_decoders,'cases':cases,'production_domain_enumerated':False}
 assert maxima=={0:0,1:5,2:10}
 assert not new_decoders and not any(c['outside_old_pencil_supports'] for c in cases)
 result['all_qualifying_decoders_belong_to_old_three_pencils']=True
 result['case_support_checks']=len(cases)*len(prepared)
 result['best_case_by_edit_count']={r:max((c for c in cases if len(c['edits'])==r),key=lambda c:c['all_projective_bad']) for r in (0,1,2)}
 if not args.verbose:result.pop('cases')
 print(json.dumps(result,indent=2))

if __name__=='__main__':main()

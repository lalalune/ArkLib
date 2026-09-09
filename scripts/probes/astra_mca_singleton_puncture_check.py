"""Exact n'=8 toy control over production P, plus parameter arithmetic.
The toy is GENERIC reduced input, provably outside the punctured rational class.
"""
import itertools,json
P=365375409332725729550921208179070755120141565953
g=303645430271030343624574566109998498685964493478
s=3;n=3*s-1;k=s;t=2*s-1
eta=pow(g,(2**30)//n,P);D=[pow(eta,i,P) for i in range(n)]
C=set(range(2*s-2));E=set(range(n))-C
u=[0 if i in C else 1 for i in range(n)]
v=[0 if i in C else D[i] for i in range(n)]
def interp(nodes,values,x):
 out=0
 for j,y in enumerate(values):
  num=den=1
  for h,z in enumerate(nodes):
   if h!=j:num=num*(x-z)%P;den=den*(nodes[j]-z)%P
  out=(out+y*num*pow(den,-1,P))%P
 return out
joint=0;bad=set();supports=0
for S in itertools.combinations(range(n),t):
 supports+=1;seed=S[:k];nodes=[D[i] for i in seed]
 a=[interp(nodes,[u[i] for i in seed],D[j]) for j in S]
 b=[interp(nodes,[v[i] for i in seed],D[j]) for j in S]
 residual=[((u[j]-a[h])%P,(v[j]-b[h])%P) for h,j in enumerate(S)]
 if all(x==0 and y==0 for x,y in residual):joint+=1;continue
 candidates=[-x*pow(y,-1,P)%P for x,y in residual if y]
 if candidates and all((x+candidates[0]*y)%P==0 for x,y in residual):bad.add(candidates[0])
assert joint==0
counted={-pow(D[i],-1,P)%P for i in E}
assert counted<=bad and len(counted)==s+1
production_s=2**28
rows=[]
for a,e in [(3*production_s-1,production_s),(3*production_s-1,production_s+1),(3*production_s,production_s)]:
 k1=2*production_s-e;t1=3*production_s-1-e;errors=a-t1;distance=a-k1+1
 rows.append(dict(length=a,dimension=k1,threshold=t1,errors=errors,minimum_distance=distance,twice_error_minus_distance=2*errors-distance))
assert [r['twice_error_minus_distance'] for r in rows]==[0,1,1]
out={'scope':'generic reduced toy over actual production prime; not structured punctured input',
 'toy':{'s':s,'n':n,'k':k,'t':t,'threshold_supports_checked':supports,
 'joint_supports':joint,'guaranteed_mca_scalars':len(counted),'exact_mca_scalar_count':len(bad)},
 'production_puncture_parameters':rows,
 'structured_class_exclusion':'first numerator would have at least 2s-2>=e roots, forcing zero'}
print(json.dumps(out))

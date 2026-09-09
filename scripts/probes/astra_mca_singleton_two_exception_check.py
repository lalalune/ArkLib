"""TOY n=16 over the actual production prime; exhaustive joint cores >=10.
This is not a production-sized instance or an over-budget construction.
"""
import itertools,json
P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
n,k,t=16,8,11
eta=pow(G,(2**30)//n,P)
D=[pow(eta,j,P) for j in range(n)]
assert len(set(D))==n and pow(eta,n,P)==1
A=list(range(11));E=list(range(11,16));Rc=A[:7];Rd=A[4:11]
def vp(roots,x):
 y=1
 for j in roots:y=y*(x-D[j])%P
 return y
c=[vp(Rc,x) for x in D];d=[vp(Rd,x) for x in D]
u=[c[i] if i in E else 0 for i in range(n)]
v=[(d[i]-c[i])%P if i in E else 0 for i in range(n)]
S0=[i for i in range(n) if u[i]==c[i]]
S1=[i for i in range(n) if (u[i]+v[i])%P==d[i]]
assert len(S0)==12 and len(S1)==12
assert len({v[i]*pow(c[i],-1,P)%P for i in E})>1
assert len({u[i]*pow(d[i],-1,P)%P for i in E})>1
# Every nonzero joint source with core >=10 has >=5 common A roots.
# For each possible root set R of size 5..7, quotient components have
# degree <=7-|R| and must jointly match >=10-|R| outside coordinates.
# Interpolate each quotient from degree+1 outside points and test the rest.
def interp(xs,ys,x):
 ans=0
 for j,y in enumerate(ys):
  num=den=1
  for h,z in enumerate(xs):
   if h!=j:num=num*(x-z)%P;den=den*(xs[j]-z)%P
  ans=(ans+y*num*pow(den,-1,P))%P
 return ans
cases=0;hits=[]
for r in range(5,8):
 degree=7-r
 for roots in itertools.combinations(A,r):
  values={i:vp(roots,D[i]) for i in E}
  invs={i:pow(values[i],-1,P) for i in E}
  for outside in itertools.combinations(E,10-r):
   cases+=1
   seeds=outside[:degree+1];xs=[D[i] for i in seeds]
   ys_u=[u[i]*invs[i]%P for i in seeds]
   ys_v=[v[i]*invs[i]%P for i in seeds]
   if all(interp(xs,ys_u,D[i])==u[i]*invs[i]%P and
          interp(xs,ys_v,D[i])==v[i]*invs[i]%P for i in outside):
    hits.append({'roots':roots,'outside':outside})
assert cases==6072
assert not hits,hits[:3]
result={'scope':'TOY n=16 over actual production P; not production n',
 'n':n,'k':k,'t':t,'zero_joint_core':11,'gamma0_agreement':12,
 'gamma1_agreement':12,'both_original_mca':True,
 'nonzero_joint_core_threshold':10,'exhaustive_candidate_cases':cases,
 'nonzero_joint_sources_at_threshold':len(hits),
 'conclusion':'Two distinct exceptional scalars do not force a second joint core >=t-1, even over the actual production prime.'}
print(json.dumps(result))

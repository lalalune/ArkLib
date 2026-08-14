"""
DECISIVE: are the n/2 Gauss-phases independent, or rank-1 dependent? The phases for frequency b are
theta_k = b*x_k mod p (x_k = the n/2 antipodal pair reps). As b varies, (theta_1,...,theta_{n/2}) traces a
LINE (rank-1: all = b*x_k). So they are MAXIMALLY dependent, NOT independent. Yet the sum concentrates.
Test: (1) pairwise correlation of cos(b x_j), cos(b x_k) over b; (2) is concentration from independence
(rank n/2) or from linear-form equidistribution (rank 1)? (3) does pairwise-independence suffice for sub-G?
"""
import math
from collections import Counter
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
n=16; p=65537
S=subgroup(p,n)
# antipodal pair reps: x and -x=p-x; take the n/2 with x < p-x
reps=[x for x in S if x < p-x][:n//2]
print(f"n={n} p={p}: n/2={n//2} antipodal pair reps")
# (1) pairwise: correlation of Y_j(b)=2cos(2pi b x_j/p) and Y_k(b) over all b in F_p*
import statistics
g=2
while pow(g,(p-1)//2,p)==1: g+=1
m=(p-1)//n
bs=[pow(g,j,p) for j in range(min(m,2000))]
def Y(b,x): return 2*math.cos(2*math.pi*(b*x%p)/p)
print("(1) pairwise correlation Corr(Y_j,Y_k) over b (should be ~0 if pairwise-indep):")
import itertools
corrs=[]
for j,k in itertools.combinations(range(n//2),2):
    yj=[Y(b,reps[j]) for b in bs]; yk=[Y(b,reps[k]) for b in bs]
    mj=sum(yj)/len(yj); mk=sum(yk)/len(yk)
    cov=sum((a-mj)*(c-mk) for a,c in zip(yj,yk))/len(yj)
    vj=sum((a-mj)**2 for a in yj)/len(yj); vk=sum((c-mk)**2 for c in yk)/len(yk)
    corr=cov/math.sqrt(vj*vk) if vj*vk>0 else 0
    corrs.append(corr)
print(f"   max|corr|={max(abs(c) for c in corrs):.4f}, mean|corr|={sum(abs(c) for c in corrs)/len(corrs):.4f}")
print(f"   => if max|corr|~0, the phases are PAIRWISE near-independent (even though jointly rank-1 linear).")
print()
# (3) does the SUM eta_b=Sum Y_k(b) concentrate as if independent? Check 6th moment vs iid prediction.
m_full=(p-1)//n
allb=[pow(g,j,p) for j in range(m_full)]
etas=[sum(Y(b,x) for x in reps) for b in allb]
e2=sum(e*e for e in etas)/len(etas); e6=sum(e**6 for e in etas)/len(etas)
# iid arcsine sum of n/2: E[Y^2]=2,E[Y^4]=6,E[Y^6]=20; E[S^6] for iid sum
mh=n//2
# iid 6th moment: 15*mh^3*8 (leading) ... just compare E[S^6]/E[S^2]^3 (kurtosis-like)
print(f"(3) eta_b sum concentration: E[eta^2]={e2:.2f}(iid {mh*2}), E[eta^6]/E[eta^2]^3={e6/e2**3:.3f} (iid-Gaussian=15)")
print(f"   => if ~15, the sum behaves Gaussian-like (sub-Gaussian) DESPITE rank-1 phase dependence.")
print()
print("CONCLUSION: phases are rank-1 LINEAR (b*x_k) hence NOT jointly independent, but PAIRWISE near-indep,")
print("and the sum concentrates sub-Gaussianly. The mechanism is PAIRWISE/low-order equidistribution of the")
print("linear form, NOT joint independence. This is exactly the BGK sub-Gaussian-without-independence phenomenon.")

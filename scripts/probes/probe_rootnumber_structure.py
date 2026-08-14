"""
Does the root-number sequence {w_chi = g(chi)/sqrt p : chi trivial on mu_n} over Z/m have EXPLOITABLE
algebraic structure (forcing cancellation = a real lead) or is it white-noise (= BGK wall)?
Tests:
 (1) AUTOCORRELATION of the phase sequence (lag k): if flat -> white noise -> BGK. If structured -> lead.
 (2) HASSE-DAVENPORT multiplicativity: w_chi1 * w_chi2 vs w_{chi1 chi2}? (HD relates Gauss sum products).
     If w is a near-CHARACTER of (Z/m), the sum S_b collapses to a geometric sum = COMPUTABLE max -> lead.
 (3) the worst b: does max_b |S_b| concentrate (a special b) or spread (generic)?
"""
import cmath, math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primroot(p):
    facs=set(); mm=p-1; d=2
    while d*d<=mm:
        while mm%d==0: facs.add(d); mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs): return g
def gauss(p,g,k):
    tot=0j; x=1; w=2*math.pi/p; wc=2*math.pi/(p-1)
    for j in range(p-1):
        tot += cmath.exp(1j*wc*k*j)*cmath.exp(1j*w*x); x=x*g%p
    return tot
n=8
p=n+1
while not(p%n==1 and isprime(p) and p>1000): p+=1
g=primroot(p); m=(p-1)//n
# w_t = g(chi_{n t})/sqrt p for t=1..m-1
W={t: gauss(p,g,(n*t)%(p-1))/math.sqrt(p) for t in range(1,m)}
print(f"n={n} p={p} m={m}")
# (1) autocorrelation A(k)=|(1/m) sum_t w_t conj(w_{t+k})|
print("(1) phase autocorrelation A(k)=|<w_t, w_{t+k}>| (flat~1/sqrt m => white noise=BGK):")
for k in (1,2,3,4,5):
    A=sum(W[t]*W[(t+k-1)%(m-1)+1].conjugate() for t in range(1,m))/(m-1)
    print(f"   k={k}: |A|={abs(A):.4f}")
print(f"   (white-noise reference 1/sqrt(m)={1/math.sqrt(m):.4f})")
# (2) HD multiplicativity: w_{t1} w_{t2} / w_{t1+t2} -- is it a clean constant (=> w is a twisted character)?
print("(2) HD-multiplicativity w_{t1}w_{t2}/w_{t1+t2} (constant modulus & phase => w is a twisted character => COLLAPSE):")
import random
random.seed(1)
ratios=[]
for _ in range(6):
    t1=random.randint(1,m-2); t2=random.randint(1,m-2)
    t3=(t1+t2-1)%(m-1)+1
    if t3 in W and abs(W[t3])>1e-9:
        r=W[t1]*W[t2]/W[t3]
        ratios.append(r)
        print(f"   t1={t1},t2={t2}: |ratio|={abs(r):.3f} phase={cmath.phase(r):.3f}")
print(f"   (if |ratio|=sqrt p const & phase structured => Gauss-sum HD relation => w semi-multiplicative)")
# (3) worst b
def S_b_ind(ind):  # b=g^ind
    tot=-1+0j
    for t in range(1,m):
        k=(n*t)%(p-1)
        tot += cmath.exp(-1j*2*math.pi*k*ind/(p-1))*W[t]*math.sqrt(p)
    return tot
Ms=[(abs((n/(p-1))*S_b_ind(ind)), ind) for ind in range(0, p-1, max(1,(p-1)//40))]
Ms.sort(reverse=True)
print(f"(3) M=max|eta_b|={Ms[0][0]:.3f} at ind={Ms[0][1]}; sqrt(n log m)={math.sqrt(n*math.log(m)):.3f}; ratio={Ms[0][0]/math.sqrt(n*math.log(m)):.3f}")

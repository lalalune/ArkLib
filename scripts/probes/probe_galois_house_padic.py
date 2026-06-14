import numpy as np, math, cmath
# Two genuinely-untried angles for M(n)=max_b|eta_b|:
# (1) GALOIS/HOUSE: eta_b are Galois conjugates; M = house (max conjugate abs value). Is house
#     determined by the NORM (computable, Habegger) or a resultant? Compute norm, house, and
#     house vs |norm|^{1/m} to see if norm pins house (it would need all conjugates EQUAL = flat).
# (2) STICKELBERGER: Gauss sum tau(chi^j) p-adic valuation = digit-sum(j). Does the p-adic structure
#     give archimedean cancellation? Check: are the period archimedean sizes correlated with the
#     p-adic (digit-sum) structure of the coset index?
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)):return g
print("Angle 1 (GALOIS/HOUSE): is the period house determined by the (computable) norm?")
print(f"{'n':>4} {'p':>8} {'m':>6} {'house=M':>9} {'min|eta|':>9} {'|norm|^(1/m)':>13} {'house/that':>11} {'flat?':>6}")
for n in [8,16,32]:
    p=int(n**4)|1
    while not(isprime(p) and (p-1)%n==0):p+=1
    g=proot(p);h=pow(g,(p-1)//n,p);m=(p-1)//n
    mu=[pow(h,i,p) for i in range(n)]
    reps=[pow(g,i,p) for i in range(m)]
    eta=np.array([sum(cmath.exp(2j*math.pi*((r*x)%p)/p) for x in mu) for r in reps])
    ab=np.abs(eta)
    house=ab.max(); mn=ab.min()
    lognorm=np.sum(np.log(np.maximum(ab,1e-300)))  # log|norm| = sum log|conjugate|
    norm_root=math.exp(lognorm/m)
    print(f"{n:>4} {p:>8} {m:>6} {house:>9.3f} {mn:>9.3f} {norm_root:>13.3f} {house/norm_root:>11.3f} {str(house/mn<1.5):>6}")
print()
print("Angle 2 (STICKELBERGER): correlation of period |eta_b| with the digit-sum (p-adic) structure")
n=16
p=int(n**4)|1
while not(isprime(p) and (p-1)%n==0):p+=1
g=proot(p);h=pow(g,(p-1)//n,p);m=(p-1)//n
mu=[pow(h,i,p) for i in range(n)]
# digit-sum of coset index i in base... the Stickelberger valuation uses base-p digits of the
# character exponent; for the n-th-power-residue characters the relevant index is i mod n's structure.
import numpy as np
eta=np.array([abs(sum(cmath.exp(2j*math.pi*((pow(g,i,p)*x)%p)/p) for x in mu)) for i in range(m)])
idx=np.arange(m)
# crude p-adic proxy: 2-adic valuation of i (since n=2^mu, the relevant structure is 2-adic)
v2=np.array([ (bin(i)[::-1].index('1') if i>0 else 20) for i in idx])
# correlation between |eta| and v2
import numpy as np
c=np.corrcoef(eta, v2)[0,1]
print(f" n={n} p={p} m={m}: corr(|eta_i|, 2adic-val(i)) = {c:.4f}  (|c|~0 => p-adic structure does NOT predict archimedean size)")
print("DONE")

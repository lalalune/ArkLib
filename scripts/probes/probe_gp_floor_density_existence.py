import numpy as np, math, sys
OUT=open(sys.argv[1],"w")
def log(s):
    OUT.write(s+"\n"); OUT.flush(); print(s,flush=True)
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    i=3
    while i*i<=q:
        if q%i==0: return False
        i+=2
    return True
def genmu(p,n):
    e=(p-1)//n
    for a in range(2,p):
        z=pow(a,e,p)
        if z!=1 and pow(z,n//2,p)!=1: return z
    return None
def Rval(n,p):
    z=genmu(p,n)
    if z is None: return None
    arr=np.zeros(p,dtype=np.float64)
    zz=1
    for i in range(n):
        arr[zz]=1.0; zz=(zz*z)%p
    S=np.abs(np.fft.rfft(arr)); S[0]=0.0
    m=(p-1)//n
    return float(S.max())/math.sqrt(2*n*math.log(m))
def scan(n, beta, count):
    p=int(n**beta)|1; Rs=[]
    while len(Rs)<count:
        if isprime(p) and (p-1)%n==0:
            r=Rval(n,p)
            if r is not None: Rs.append((p,r))
        p+=2
    return Rs
import statistics
for (n,beta,cnt) in [(64,4.0,60)]:
    Rs=scan(n,beta,cnt)
    vals=sorted(r for _,r in Rs)
    pmax,rmax=max(Rs,key=lambda t:t[1])
    log(f"n={n} beta={beta} primes={len(Rs)}: min={vals[0]:.3f} med={vals[len(vals)//2]:.3f} max={vals[-1]:.3f} mean={statistics.mean(vals):.3f}")
    log(f"  worst prime p={pmax} R={rmax:.4f}")
    log(f"  frac(R>1)={sum(1 for v in vals if v>1)/len(vals):.3f}  frac(R>1.1)={sum(1 for v in vals if v>1.1)/len(vals):.3f}  frac(R<0.95)={sum(1 for v in vals if v<0.95)/len(vals):.3f}")
log("DONE")
OUT.close()

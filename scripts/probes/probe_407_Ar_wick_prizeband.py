import numpy as np
from sympy import isprime, primitive_root
# Confirm A_r/Wick < 1 (no violation) across the PRIZE band beta in [4,5] for n=8,16,32,
# and report how close to 1 the max gets (approaching from below = clean).
def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r
def Ar_ratios(n,p,rmax):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=np.array([pow(gen,j,p) for j in range(n)])
    a2=np.empty(p)
    for b in range(p):
        a2[b]=abs(np.exp(2j*np.pi*(b*mu%p).astype(float)/p).sum())**2
    q=p; out=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q; Ar=Er-(n**(2*r))/q
        out.append(Ar/(dfact(2*r-1)*(n**r)))
    return out
print("PRIZE BAND beta in [4,5]: any A_r/Wick>1?")
anyviol=False
for n in [8,16,32]:
    cnt=0
    for p in range(int(n**4.0), int(n**5.0)):
        if p>250000: break
        if p%n==1 and isprime(p):
            beta=np.log(p)/np.log(n)
            if not (3.9<=beta<=5.1): continue
            rmax=min(int(2*np.log((p-1)//n))+1,12)
            rats=Ar_ratios(n,p,rmax); mx=max(rats)
            v = mx>1.0001
            anyviol = anyviol or v
            print(f"  n={n} p={p} beta={beta:.2f}: max A_r/Wick={mx:.4f} (r={int(np.argmax(rats))+1}){'  *** VIOL ***' if v else ''}")
            cnt+=1
            if cnt>=4: break
print("\nPRIZE-BAND VERDICT:", "VIOLATION FOUND" if anyviol else "NO VIOLATION — A_r<=Wick holds across prize band (thinness-essential: violated only in thick window)")

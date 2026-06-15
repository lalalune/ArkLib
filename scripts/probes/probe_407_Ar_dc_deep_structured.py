import numpy as np
from sympy import isprime, primitive_root, factorint

# CRUX TEST: does the DC-subtracted A_r cross Wick at DEEP r (~log m) at STRUCTURED prize primes
# (Fermat-type, high 2-adic valuation of p-1 = the campaign's named adversaries)? The orchestrator's
# confirm-probe (no catch-up, n=32..256) used clean primes; the issue (c.150) says raw E_r crosses
# Wick at r~log m at STRUCTURED primes. Question: is DC subtraction enough to keep A_r<=Wick at deep r
# at the adversarial structured primes, or does A_r ALSO cross there?

def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def Ar_profile(n, p, rmax):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=np.array([pow(gen,j,p) for j in range(n)])
    a2=np.empty(p)
    for b in range(p):
        a2[b]=abs(np.exp(2j*np.pi*((b*mu)%p).astype(float)/p).sum())**2
    q=p; out=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q
        Ar=Er-(n**(2*r))/q
        out.append((r, Ar/(dfact(2*r-1)*n**r)))
    return out

# Structured prize primes: p-1 with high 2-part, p ~ n^4. Fermat 65537 = 2^16+1 (v2=16).
tests = [
    (16, 65537),   # Fermat, beta=4.0, v2(p-1)=16 (max structure)
    (8, 7681),     # 7681-1 = 7680 = 2^9 * 15, v2=9, beta~4.3 for n=8
    (8, 12289),    # 12289-1 = 12288 = 2^12 * 3, v2=12, beta~4.5, high 2-part
    (32, 65537),   # n=32 in Fermat field, beta=3.2 (thick-ish but structured)
]
for n,p in tests:
    if (p-1)%n!=0 or not isprime(p):
        print(f"skip n={n} p={p} (not valid)"); continue
    m=(p-1)//n; v2=factorint(p-1).get(2,0)
    rmax=min(int(2*np.log(m))+2, 14)
    prof=Ar_profile(n,p,rmax)
    beta=np.log(p)/np.log(n); logm=np.log(m)
    mx=max(prof,key=lambda t:t[1])
    cross=[r for r,rat in prof if rat>1.0001]
    print(f"n={n} p={p} beta={beta:.2f} v2(p-1)={v2} m={m} logm={logm:.1f}: max A_r/Wick={mx[1]:.4f}@r={mx[0]}  cross r={cross if cross else 'NONE'}")
    for r,rat in prof:
        tag="  <-- r~logm" if abs(r-logm)<1 else ""
        if rat>0.5 or tag:
            print(f"    r={r}: A_r/Wick={rat:.4f}{tag}")

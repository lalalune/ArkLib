import numpy as np
from sympy import isprime, primitive_root, factorint
# HUNT for A_r > Wick (would refute the load-bearing DC hypothesis A_r<=Wick).
# Sweep: multiple n=2^a, multiple primes per n across beta in [2,5], INCLUDING structured
# Fermat-type primes (p = k*2^a + 1 with small k) where cyclotomic structure is richest.
# Also check r=1 edge carefully (A_1 = q n - n^2, Wick_1 = n => ratio = (qn-n^2)/n = q - n).
# Wait: that's HUGE. Let me recompute A_r/Wick at r=1 exactly.

def dfact(k):
    r=1.0
    while k>1: r*=k; k-=2
    return r

def all_primes(n, beta_lo, beta_hi, maxp=200000, want=6):
    out=[]
    lo=int(n**beta_lo); hi=min(int(n**beta_hi), maxp)
    p=lo + ((-lo)% n) +1 if (lo%n!=1) else lo
    # just scan
    for p in range(lo, hi):
        if p%n==1 and isprime(p):
            out.append(p)
            if len(out)>=want: break
    return out

def Ar_over_wick(n,p,rmax):
    h=(p-1)//n; g=primitive_root(p); gen=pow(g,h,p)
    mu=np.array([pow(gen,j,p) for j in range(n)])
    a2=np.empty(p)
    for b in range(p):
        a2[b]=abs(np.exp(2j*np.pi*(b*mu % p)/p).sum())**2
    q=p; res=[]
    for r in range(1,rmax+1):
        Er=(a2**r).sum()/q
        Ar=Er-(n**(2*r))/q
        Wick=dfact(2*r-1)*(n**r)
        res.append((r, Ar/Wick))
    return res

print("HUNT: any A_r/Wick > 1 ?  (r=1 first to sanity-check the edge)")
viol=[]
for n in [8,16,32]:
    for p in all_primes(n, 2.0, 5.0, maxp=80000, want=5):
        rmax=min(int(2*np.log((p-1)//n))+1, 14)
        res=Ar_over_wick(n,p,rmax)
        mx=max(res, key=lambda t:t[1])
        beta=np.log(p)/np.log(n)
        k=(p-1)//n  # p = k*n+... actually p-1 = ? structured if p-1=k*2^a
        is_struct = (factorint(p-1).get(2,0) >= np.log2(n))
        print(f"n={n} p={p} beta={beta:.2f} struct2={is_struct}: max A_r/Wick = {mx[1]:.4f} at r={mx[0]}  (r=1: {res[0][1]:.4f})")
        for r,ratio in res:
            if ratio>1.0001: viol.append((n,p,r,ratio))
print("\nVIOLATIONS (A_r>Wick):", viol if viol else "NONE FOUND — A_r<=Wick holds across the sweep")

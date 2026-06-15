import numpy as np
from sympy import isprime, primitive_root
def maxeta(p,n):
    g=primitive_root(p); m=(p-1)//n; cur=pow(g,m,p)
    a=np.zeros(p); x=1
    for j in range(n): a[x]=1.0; x=(x*cur)%p
    F=np.fft.fft(a); F[0]=0; return float(np.max(np.abs(F)))
def v2(x):
    c=0
    while x%2==0: x//=2;c+=1
    return c
# n=32 strict prize band beta>=4: sample ~40 primes (don't sweep all). p>=n^4.
n=32; plo=n**4
print(f"n={n} prize band beta>=4 (p>={plo}); sample 40 primes, m_odd flagged",flush=True)
Cs=[]; m=plo//n + (1 if (plo//n)%2==0 else 0)
while len(Cs)<40 and m<200000:
    p=m*n+1
    if p>9_000_000: break
    if isprime(p):
        C=maxeta(p,n)/np.sqrt(2*n*np.log(p/n))
        beta=np.log(p)/np.log(n)
        Cs.append((C,p,m%2,v2(p-1),beta))
    m+= 1
arr=np.array([c[0] for c in Cs])
print(f"  #={len(arr)} median={np.median(arr):.3f} worst={arr.max():.3f} #>1={int((arr>1).sum())} #>1.2={int((arr>1.2).sum())} #>1.41={int((arr>1.414).sum())}",flush=True)
mo=[c[0] for c in Cs if c[2]==1]; me=[c[0] for c in Cs if c[2]==0]
if mo: print(f"  m_odd  (v2=5): #={len(mo)} worst={max(mo):.3f}",flush=True)
if me: print(f"  m_even (v2>5): #={len(me)} worst={max(me):.3f}",flush=True)
# show the worst one
w=max(Cs); print(f"  WORST: C={w[0]:.3f} p={w[1]} m_parity={'odd' if w[2] else 'even'} v2(p-1)={w[3]} beta={w[4]:.2f}",flush=True)
